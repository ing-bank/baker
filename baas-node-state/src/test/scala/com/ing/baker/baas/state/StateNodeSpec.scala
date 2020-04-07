package com.ing.baker.baas.state

import java.net.InetSocketAddress
import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import cats.effect.{IO, Resource}
import cats.implicits._
import com.ing.baker.baas.mocks.{EventListener, KubeApiServer, RemoteComponents, RemoteInteraction}
import com.ing.baker.baas.recipe.Events.{ItemsReserved, OrderPlaced}
import com.ing.baker.baas.recipe.Ingredients.{Item, OrderId, ReservedItems}
import com.ing.baker.baas.recipe.{Interactions, ItemReservationRecipe}
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.baas.testing.BakeryFunSpec
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.typesafe.config.ConfigFactory
import org.mockserver.integration.ClientAndServer
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers
import skuber.api.client.KubernetesClient

import scala.concurrent.Future

class StateNodeSpec extends BakeryFunSpec with Matchers {

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

  describe("Bakery State Node") {

    test("Recipe management") { context =>
      for {
        recipeInformation <- io(context.client.getRecipe(recipeId))
        noSuchRecipeError <- io(context.client
          .getRecipe("non-existent")
          .map(_ => None)
          .recover { case e: BakerException => Some(e) })
        allRecipes <- io(context.client.getAllRecipes)
      } yield {
        recipeInformation.compiledRecipe shouldBe recipe
        noSuchRecipeError shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
        allRecipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(recipe)
      }
    }

    test("Baker.bake") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        state <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        _ <- eventually { context.eventListener.verifyNoEventsArrived }
      } yield {
        state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    test("Baker.bake (fail with ProcessAlreadyExistsException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
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
        e <- io(context.client
          .bake("non-existent", recipeInstanceId)
          .map(_ => None)
          .recover { case e => Some(e) })
      } yield e shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
    }

    test("Baker.getRecipeInstanceState (fails with NoSuchProcessException)") { context =>
      for {
        e <- io(context.client
          .getRecipeInstanceState("non-existent")
          .map(_ => None)
          .recover { case e: BakerException => Some(e) })
      } yield e shouldBe Some(BakerException.NoSuchProcessException("non-existent"))
    }

    test("Baker.fireEventAndResolveWhenReceived") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        status <- io(context.client.fireEventAndResolveWhenReceived(recipeInstanceId, OrderPlacedEvent))
      } yield status shouldBe SensoryEventStatus.Received
    }

    test("Baker.fireEventAndResolveWhenCompleted") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        result <- io(context.client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent))
        serverState <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        _ <- eventually { context.eventListener.verifyEventsReceived(2) }
      } yield {
        result.eventNames shouldBe Seq("OrderPlaced", "ItemsReserved")
        serverState.events.map(_.name) shouldBe Seq("OrderPlaced", "ItemsReserved")
      }
    }

    test("Baker.fireEventAndResolveWhenCompleted (fails with IllegalEventException)") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      val event = EventInstance("non-existent", Map.empty)
      for {
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        result <- io(context.client
          .fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          .map(_ => None)
          .recover { case e: BakerException => Some(e) })
        serverState <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        _ <- context.remoteInteraction.didNothing
      } yield {
        result shouldBe Some(BakerException.IllegalEventException("No event with name 'non-existent' found in recipe 'ItemReservation.recipe'"))
        serverState.events.map(_.name) should not contain("OrderPlaced")
      }
    }

    test("Baker.fireEventAndResolveOnEvent") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        result <- io(context.client.fireEventAndResolveOnEvent(recipeInstanceId, OrderPlacedEvent, "OrderPlaced"))
        _ <- eventually {
          for {
            serverState <- io(context.client.getRecipeInstanceState(recipeInstanceId))
          } yield serverState.events.map(_.name) shouldBe Seq("OrderPlaced", "ItemsReserved")
        }
        _ <-  eventually {  context.eventListener.verifyEventsReceived(2) }
      } yield result.eventNames shouldBe Seq("OrderPlaced")
    }

    test("Baker.getAllRecipeInstancesMetadata") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        clientMetadata <- io(context.client.getAllRecipeInstancesMetadata)
        serverMetadata <- io(context.client.getAllRecipeInstancesMetadata)
      } yield clientMetadata shouldBe serverMetadata
    }

    test("Baker.getVisualState") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        _ <- io(context.client.getVisualState(recipeInstanceId))
      } yield succeed
    }

    test("Baker.retryInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- io(context.client.bake(recipeIdBlocking, recipeInstanceId))
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- io(context.client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent))
        state1 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- context.remoteInteraction.processesSuccessfullyAndFires(ItemsReservedEvent)
        _ <- io(context.client.retryInteraction(recipeInstanceId, "ReserveItems"))
        state2 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- eventually {  context.eventListener.verifyEventsReceived(2) }
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain("ItemsReserved")
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
          _ <- io(context.client.bake(recipeIdBlocking, recipeInstanceId))
          _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
          _ <- io(context.client.fireEventAndResolveWhenCompleted(recipeInstanceId, OrderPlacedEvent))
          state1 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
          _ <- io(context.client.resolveInteraction(recipeInstanceId, "ReserveItems", resolutionEvent))
          state2data <- io(context.client.getRecipeInstanceState(recipeInstanceId))
          state2 = state2data.events.map(_.name)
          eventState = state2data.ingredients.get("reservedItems").map(_.as[ReservedItems].items.head.itemId)
          // TODO Currently the event listener receives the OrderPlaced... shouldn't also receive the resolved event?
          _ <-  eventually {  context.eventListener.verifyEventsReceived(1) }
        } yield {
          state1 should contain("OrderPlaced")
          state1 should not contain("ItemsReserved")
          state2 should contain("OrderPlaced")
          state2 should contain("ItemsReserved")
          eventState shouldBe Some("resolution-item")
        }
    }

    test("Baker.stopRetryingInteraction") { context =>
      val recipeInstanceId: String = UUID.randomUUID().toString
      for {
        _ <- io(context.client.bake(recipeId, recipeInstanceId))
        _ <- context.remoteInteraction.processesWithFailure(new RuntimeException("functional failure"))
        _ <- io(context.client.fireEventAndResolveWhenReceived(recipeInstanceId, OrderPlacedEvent))
        state1 <- io(context.client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name)))
        _ <- io(context.client.stopRetryingInteraction(recipeInstanceId, "ReserveItems"))
        state2data <- io(context.client.getRecipeInstanceState(recipeInstanceId))
        state2 = state2data.events.map(_.name)
        _ <-  eventually {  context.eventListener.verifyEventsReceived(1) }
      } yield {
        state1 should contain("OrderPlaced")
        state1 should not contain("ItemsReserved")
        state2 should contain("OrderPlaced")
        state2 should not contain("ItemsReserved")
      }
    }
  }

  case class Context(
    client: Baker,
    remoteComponents: RemoteComponents,
    remoteInteraction: RemoteInteraction,
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

    val interactionInstance: InteractionInstance =
      InteractionInstance(
        name = Interactions.ReserveItemsInteraction.name,
        input = Interactions.ReserveItemsInteraction.inputIngredients.map(_.ingredientType),
        run = _ => ??? // We never call this because it is mocked by mock server
      )

    for {
      // Mock server
      mockServer <- Resource.make(IO(ClientAndServer.startClientAndServer(0)))(s => IO(s.stop()))
      remoteInteraction = new RemoteInteraction(mockServer, interactionInstance)
      kubeApiServer = new KubeApiServer(mockServer)
      remoteComponents = new RemoteComponents(kubeApiServer, remoteInteraction)
      _ <- Resource.liftF(remoteComponents.registerToTheCluster)

      makeActorSystem = IO {
        ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
          """
            |akka {
            |  stdout-loglevel = "OFF"
            |  loglevel = "OFF"
            |}
            |""".stripMargin)) }
      stopActorSystem = (system: ActorSystem) => IO.fromFuture(IO {
        system.terminate().flatMap(_ => system.whenTerminated) }).void
      system <- Resource.make(makeActorSystem)(stopActorSystem)
      materializer = ActorMaterializer()(system)

      k8s: KubernetesClient = skuber.k8sInit(skuber.api.Configuration.useLocalProxyOnPort(mockServer.getLocalPort))(system, materializer)
      serviceDiscovery <- ServiceDiscovery.resource(executionContext, k8s)(contextShift, timer, system, materializer)
      eventListener = new EventListener()
      baker = AkkaBaker
        .withConfig(AkkaBakerConfig.localDefault(system).copy(
          interactionManager = serviceDiscovery.buildInteractionManager,
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings(
            allowAddingRecipeWithoutRequiringInstances = true))(system))

      _ <- Resource.liftF(eventListener.eventSink.attach(baker))
      _ <- Resource.liftF(RecipeLoader.loadRecipesIntoBaker(getResourceDirectoryPathSafe, baker))
      _ <- Resource.liftF(eventually(serviceDiscovery.cacheInteractions.get.map(data =>
        assert(data.headOption.map(_.name).contains(Interactions.ReserveItemsInteraction.name)))))

      server <- StateNodeService.resource(baker, getResourceDirectoryPathSafe, InetSocketAddress.createUnresolved("127.0.0.1", 0))
      client <- BakerClient.resource(server.baseUri, executionContext)

    } yield Context(
      client,
      remoteComponents,
      remoteInteraction,
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

