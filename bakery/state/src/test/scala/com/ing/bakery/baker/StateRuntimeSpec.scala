package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.common.{BakerException, RecipeRecord, SensoryEventStatus}
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstanceDescriptor, InteractionInstanceInput}
import com.ing.baker.types.{ByteArray, CharArray, ListType, RecordField, RecordType}
import com.ing.bakery.mocks.{EventListener, KubeApiServer, RemoteInteraction}
import com.ing.bakery.recipe.Events.{ItemsReserved, OrderPlaced}
import com.ing.bakery.recipe.Ingredients.{Item, OrderId, ReservedItems}
import com.ing.bakery.recipe.{ItemReservationRecipe, SimpleRecipe}
import com.ing.bakery.scaladsl.BakerClient
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.mockserver.integration.ClientAndServer
import org.scalatest.ConfigMap
import org.scalatest.compatible.Assertion
import org.scalatest.matchers.should.Matchers

import java.net.InetSocketAddress
import java.util.UUID
import scala.concurrent.Future

class StateRuntimeSpec extends BakeryFunSpec with Matchers {

  val recipe: CompiledRecipe =
    ItemReservationRecipe.compiledRecipe

  val recipeId: String = recipe.recipeId

  val recipeWithBlockingStrategy: CompiledRecipe =
    ItemReservationRecipe.compiledRecipeWithBlockingStrategy

  val recipeIdBlocking: String = recipeWithBlockingStrategy.recipeId

  val OrderPlacedEvent: EventInstance =
    EventInstance.unsafeFrom(
      OrderPlaced(OrderId("order-1"), List(Item("item-1"))
      ))

  val ItemsReservedEvent: EventInstance =
    EventInstance.unsafeFrom(
      ItemsReserved(ReservedItems(
        List(Item("item-1")),
        Array.fill(1)(Byte.MaxValue)
      )))

  def io[A](f: => Future[A]): IO[A] =
    IO.fromFuture(IO(f))

  def awaitForInteractionDiscovery(context: Context): IO[Assertion] =
    awaitForServiceDiscoveryState(context)(_.map(_.name) shouldBe List("TimerInteraction", "TimerInteraction", "ReserveItems"))

  def awaitForEmptyServiceDiscovery(context: Context): IO[Assertion] =
    awaitForServiceDiscoveryState(context)(_.map(_.name) shouldBe List("TimerInteraction", "TimerInteraction"))

  def awaitForServiceDiscoveryState(context: Context)(f: List[InteractionInstance[IO]] => Assertion): IO[Assertion] =
    eventually(
      context.interactions.listAll.map(f)
    )

  describe("Service Discovery") {

    test("Simple interaction discovery") { context =>
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- context.kubeApiServer.deleteInteraction()
        _ <- awaitForEmptyServiceDiscovery(context)
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
      } yield succeed
    }

    test("No interaction discovery from other scope") { context =>
      for {
        _ <- awaitForEmptyServiceDiscovery(context)
        _ <- context.kubeApiServer.deployInteraction("wrongscope")
        _ <- awaitForEmptyServiceDiscovery(context)
      } yield succeed
    }

  }

  describe("Bakery Baker") {

    test("Recipe management") { context =>
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        recipeInformation <- io(context.client.getRecipe(recipeId))
        interactionInformation <- io(context.client.getInteraction("ReserveItems"))
        noSuchRecipeError <- io(context.client
          .getRecipe("nonexistent")
          .map(_ => None)
          .recover { case e: BakerException => Some(e) })
        allRecipes <- io(context.client.getAllRecipes)
      } yield {
        recipeInformation.compiledRecipe.name shouldBe recipe.name
        interactionInformation shouldBe Some(
          InteractionInstanceDescriptor("ReserveItems",
            Seq(InteractionInstanceInput(Option.apply("orderId"), RecordType(Seq(RecordField("orderId", CharArray)))),
              InteractionInstanceInput(Option.apply("items"), ListType(RecordType(Seq(RecordField("itemId", CharArray)))))
            ), Some(Map(
              "OrderHadUnavailableItems" -> Map("unavailableItems" -> ListType(RecordType(Seq(RecordField("itemId", CharArray))))),
              "ItemsReserved" -> Map("reservedItems" -> RecordType(Seq(RecordField("items",
                ListType(RecordType(Seq(RecordField("itemId", CharArray))))), RecordField("data", ByteArray))))
            ))
          )
        )
        noSuchRecipeError shouldBe Some(BakerException.NoSuchRecipeException("nonexistent"))
        allRecipes.get(recipeId).map(_.compiledRecipe.name) shouldBe Some(recipe.name)
        allRecipes.get(SimpleRecipe.compiledRecipe.recipeId).map(_.compiledRecipe.name) shouldBe Some("Simple")
      }
    }

    test("Baker.bake") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        state <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        _ <- eventually {
          context.eventListener.verifyNoEventsArrived
        }
      } yield {
        state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    test("Baker.bake (fail with ProcessAlreadyExistsException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        e <- io(context.client
          .bake(recipeId, recipeInstanceId)
          .map(_ => None)
          .recover { case e: BakerException => Some(e) })
        state <- io(context.client.getRecipeInstanceState(recipeInstanceId))
      } yield {
        e shouldBe Some(BakerException.ProcessAlreadyExistsException(recipeInstanceId))
        state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    test("Baker.bake (fail with NoSuchRecipeException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        e <- io(context.client
          .bake("nonexistent", recipeInstanceId)
          .map(_ => None)
          .recover { case e => Some(e) })
      } yield e shouldBe Some(BakerException.NoSuchRecipeException("nonexistent"))
    }

    test("Baker.getRecipeInstanceState (fails with NoSuchProcessException)") { context =>
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        e <- io(context.client
          .getRecipeInstanceState("nonexistent")
          .map(_ => None)
          .recover { case e => Some(e) })
      } yield {
        e shouldBe Some(NoSuchProcessException("UNKNOWN"))
      }
    }

    test("Baker.getRecipeInstanceState with SQL injection (fails with error 404)") { context =>
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        e <- io(context.client
          .getRecipeInstanceState("select * from sometable")
          .map(_ => None)
          .recover { case e => Some(e) })
      } yield e shouldBe Some(NoSuchProcessException("UNKNOWN"))
    }

    test("Baker.fireEventAndResolveWhenReceived") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        status <- io(context.client.fireEventAndResolveWhenReceived(recipeInstanceId, OrderPlacedEvent))
      } yield status shouldBe SensoryEventStatus.Received
    }


    test("Baker.fireEventAndResolveWhenCompleted (fails with IllegalEventException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      val event = EventInstance("nonexistent", Map.empty)
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        result <- io(context.client
          .fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          .map(_ => None)
          .recover { case e: BakerException => Some(e) })
        serverState <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        _ <- context.remoteInteraction.didNothing
      } yield {
        result shouldBe Some(BakerException.IllegalEventException("No event with name 'nonexistent' found in recipe 'ItemReservation.recipe'"))
        serverState.events.map(_.name) should not contain ("OrderPlaced")
      }
    }

    test("Baker.fireEventAndResolveOnEvent") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        result <- io(context.client.fireEventAndResolveOnEvent(recipeInstanceId, OrderPlacedEvent, "OrderPlaced"))
        _ <- eventually {
          for {
            serverState <- io(context.client.getRecipeInstanceState(recipeInstanceId))
          } yield serverState.events.map(_.name) shouldBe Seq("OrderPlaced", "ItemsReserved")
        }
        _ <- eventually {
          context.eventListener.verifyEventsReceived(2)
        }
      } yield result.eventNames shouldBe Seq("OrderPlaced")
    }

    test("Baker.getAllRecipeInstancesMetadata") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        clientMetadata <- io(context.client.getAllRecipeInstancesMetadata)
        serverMetadata <- io(context.client.getAllRecipeInstancesMetadata)
      } yield clientMetadata shouldBe serverMetadata
    }

    test("Baker.getVisualState") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        _ <- io(context.client.getVisualState(recipeInstanceId))
      } yield succeed
    }

    test("Baker.retryInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- io(context.client.bake(recipeIdBlocking, recipeInstanceId))
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- io(context.client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent))
        state1 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.retryInteraction(recipeInstanceId, "ReserveItems"))
        state2 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- eventually {
          context.eventListener.verifyEventsReceived(2)
        }
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain ("ItemsReserved")
        state2 should contain("OrderPlaced")
        state2 should contain("ItemsReserved")
      }
    }

    test("Baker.resolveInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      val resolutionEvent = EventInstance.unsafeFrom(
        ItemsReserved(reservedItems = ReservedItems(items = List(Item("resolution-item")), data = Array.empty))
      )
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- io(context.client.bake(recipeIdBlocking, recipeInstanceId))
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- io(context.client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent))
        state1 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- io(context.client.resolveInteraction(recipeInstanceId, "ReserveItems", resolutionEvent))
        state2data <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        state2 = state2data.events.map(_.name)
        eventState = state2data.ingredients.get("reservedItems").map(_.as[ReservedItems].items.head.itemId)
        // TODO Currently the event listener receives the OrderPlaced... shouldn't also receive the resolved event?
        _ <- eventually {
          context.eventListener.verifyEventsReceived(1)
        }
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain ("ItemsReserved")
        state2 should contain("OrderPlaced")
        state2 should contain("ItemsReserved")
        eventState shouldBe Some("resolution-item")
      }
    }

    test("Baker.stopRetryingInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.respondsWithInterfaces()
        _ <- context.kubeApiServer.deployInteraction()
        _ <- awaitForInteractionDiscovery(context)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- io(context.client.fireEventAndResolveWhenReceived(recipeInstanceId, OrderPlacedEvent))
        state1 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- io(context.client.stopRetryingInteraction(recipeInstanceId, "ReserveItems"))
        state2data <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        state2 = state2data.events.map(_.name)
        _ <- eventually {
          context.eventListener.verifyEventsReceived(1)
        }
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain ("ItemsReserved")
        state2 should contain("OrderPlaced")
        state2 should not contain ("ItemsReserved")
      }
    }
  }

  test("Baker.fireEventAndResolveWhenCompleted") { context =>
    val recipeInstanceId: String = UUID.randomUUID().toString
    for {
      _ <- context.remoteInteraction.respondsWithInterfaces()
      _ <- context.kubeApiServer.deployInteraction()
      _ <- awaitForInteractionDiscovery(context)
      _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
      _ <- io(context.client.bake(recipeId, recipeInstanceId))
      result <- io(context.client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent))
      serverState <- io(context.client.getRecipeInstanceState(recipeInstanceId))
      _ <- eventually {
        context.eventListener.verifyEventsReceived(2)
      }
    } yield {
      serverState.events.map(_.name) shouldBe Seq("OrderPlaced", "ItemsReserved")
      result.eventNames shouldBe Seq("OrderPlaced", "ItemsReserved")
    }
  }


  case class Context(
                      client: Baker,
                      remoteInteraction: RemoteInteraction,
                      interactions: InteractionManager[IO],
                      eventListener: EventListener,
                      kubeApiServer: KubeApiServer
                    )

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = Unit

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] = {

    def getResourceDirectoryPathSafe: String = {
      val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
      val safePath = getClass.getResource("/recipes").getPath
      if (isWindows) safePath.tail
      else safePath
    }

    val config = ConfigFactory.parseString(
      """
        |akka {
        |  stdout-loglevel = "OFF"
        |  loglevel = "OFF"
        |}
        |baker.interactions.pod-label-selector = "scope=webshop"
        |baker.interactions.api-url-prefix = "/api/bakery/interactions"
        |""".stripMargin)

    for {
      // Mock server
      mockServer <- Resource.make(IO(ClientAndServer.startClientAndServer(0)))(s => IO(s.stop()))
      remoteInteraction = new RemoteInteraction(mockServer)
      kubeApiServer = new KubeApiServer(mockServer)
      _ <- Resource.eval(kubeApiServer.noNewInteractions()) // Initial setup so that the service discovery component has something to query to immediately

      makeActorSystem = IO { ActorSystem(UUID.randomUUID().toString, config) }
      stopActorSystem = (system: ActorSystem) => IO.fromFuture(IO {
        system.terminate().flatMap(_ => system.whenTerminated)
      }).void
      system <- Resource.make(makeActorSystem)(stopActorSystem)
      interactions <- new BaseInteractionRegistry(config, system) {
        override protected def remoteHttpInteractionManagers(client: Client[IO]): List[Resource[IO, DynamicInteractionManager]] =
          List(new KubernetesInteractions(config, system,
            client, skuber.k8sInit(skuber.api.Configuration.useLocalProxyOnPort(mockServer.getLocalPort))(system)) {
          }.resource)
      }.resource
      recipeAddingCache = new RecipeCache {
        override def merge(recipes: List[RecipeRecord]): IO[List[RecipeRecord]] =
          IO(RecipeRecord.of(SimpleRecipe.compiledRecipe) ::
            recipes.filter(_.recipeId != SimpleRecipe.compiledRecipe.recipeId))
      }
      eventListener = new EventListener()
      baker = AkkaBaker
        .withConfig(AkkaBakerConfig.localDefault(system).copy(
          interactions = interactions,
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings(
            allowAddingRecipeWithoutRequiringInstances = true))(system)
        )

      _ <- Resource.eval(eventListener.eventSink.attach(baker))
      _ <- Resource.eval(RecipeLoader.loadRecipesIntoBaker(getResourceDirectoryPathSafe, recipeAddingCache, baker))

      server <- BakerService.resource(baker, InetSocketAddress.createUnresolved("127.0.0.1", 0), "/api/bakery", "/opt/docker/dashboard", loggingEnabled = true)
      client <- BakerClient.resource(server.baseUri, "/api/bakery", executionContext)

    } yield Context(
      client,
      remoteInteraction,
      interactions,
      eventListener,
      kubeApiServer
    )
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()

}

