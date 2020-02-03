package com.ing.baker.baas.spec

import java.util.UUID

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.baas.common.RemoteInteraction
import com.ing.baker.baas.recipe.CheckoutFlowEvents.ItemsReserved
import com.ing.baker.baas.recipe.CheckoutFlowIngredients.{Item, OrderId, ReservedItems, ShippingAddress}
import com.ing.baker.baas.recipe._
import com.ing.baker.baas.scaladsl.{RemoteEventListener, BakerClient, RemoteInteraction}
import com.ing.baker.baas.spec.BaaSIntegrationSpec._
import com.ing.baker.baas.state.BaaSServer
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, Baker => ScalaBaker}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.{Config, ConfigFactory}
import org.jboss.netty.channel.ChannelException
import org.scalatest._

import scala.collection.mutable
import scala.concurrent.{ExecutionContext, Future}

class BaaSIntegrationSpec
  extends AsyncFunSpec
    with Matchers
    with BeforeAndAfterAll
    with BeforeAndAfterEach {

  val test: IntegrationTest = BaaSIntegrationSpec.testWith

  implicit val timer: Timer[IO] = IO.timer(executionContext)

  describe("Baker Client-Server") {
    it("Baker.addRecipe") {
      test { (client, stateNode, interactionNode, _) =>
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- stateNode.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getRecipe") {
      test { (client, _, interactionNode, _) =>
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- client.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getRecipe (fail with NoSuchRecipeException)") {
      test { (client, _, _, _) =>
        for {
          e <- client
            .getRecipe("non-existent")
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
      }
    }

    it("Baker.getAllRecipes") {
      test { (client, stateNode, interactionNode, _) =>
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          recipes <- client.getAllRecipes
        } yield recipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(compiledRecipe)
      }
    }

    it("Baker.bake") {
      test { (client, stateNode, interactionNode, eventListenerNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          events <- setupEventListener(compiledRecipe, eventListenerNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          state <- stateNode.getRecipeInstanceState(recipeInstanceId)
        } yield {
          events.toList shouldBe List.empty
          state.recipeInstanceId shouldBe recipeInstanceId
        }
      }
    }

    it("Baker.bake (fail with ProcessAlreadyExistsException)") {
      test { (client, stateNode, interactionNode, _) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          e <- client
            .bake(recipeId, recipeInstanceId)
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
          state <- stateNode.getRecipeInstanceState(recipeInstanceId)
        } yield {
          e shouldBe Some(BakerException.ProcessAlreadyExistsException(recipeInstanceId))
          state.recipeInstanceId shouldBe recipeInstanceId
        }
      }
    }

    it("Baker.bake (fail with NoSuchRecipeException)") {
      test { (client, _, _, _) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          e <- client
            .bake("non-existent", recipeInstanceId)
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
      }
    }

    it("Baker.getRecipeInstanceState (fails with NoSuchProcessException)") {
      test { (_, stateNode, _, _) =>
        for {
          e <- stateNode
            .getRecipeInstanceState("non-existent")
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchProcessException("non-existent"))
      }
    }

    it("Baker.fireEventAndResolveWhenReceived") {
      test { (client, _, interactionNode, _) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          status <- client.fireEventAndResolveWhenReceived(recipeInstanceId, event)
        } yield status shouldBe SensoryEventStatus.Received
      }
    }

    it("Baker.fireEventAndResolveWhenCompleted") {
      test { (client, stateNode, interactionNode, eventListenerNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          events <- setupEventListener(compiledRecipe, eventListenerNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          result <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          serverState <- stateNode.getRecipeInstanceState(recipeInstanceId)
        } yield {
          result.eventNames should contain("ShippingAddressReceived")
          serverState.events.map(_.name) should contain("ShippingAddressReceived")
          events.toList.map(_.name) should contain("ShippingAddressReceived")
        }
      }
    }

    it("Baker.fireEventAndResolveWhenCompleted (fails with IllegalEventException)") {
      test { (client, stateNode, interactionNode, _) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance("non-existent", Map.empty)
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          result <- client
              .fireEventAndResolveWhenCompleted(recipeInstanceId, event)
              .map(_ => None)
              .recover { case e: BakerException => Some(e) }
          serverState <- stateNode.getRecipeInstanceState(recipeInstanceId)
        } yield {
          result shouldBe Some(BakerException.IllegalEventException("No event with name 'non-existent' found in recipe 'Webshop'"))
          serverState.events.map(_.name) should not contain("ShippingAddressReceived")
        }
      }
    }

    it("Baker.fireEventAndResolveOnEvent") {
      test { (client, stateNode, interactionNode, eventListenerNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          events <- setupEventListener(compiledRecipe, eventListenerNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          result <- client.fireEventAndResolveOnEvent(recipeInstanceId, event, "ShippingAddressReceived")
          serverState <- stateNode.getRecipeInstanceState(recipeInstanceId)
        } yield {
          result.eventNames should contain("ShippingAddressReceived")
          serverState.events.map(_.name) should contain("ShippingAddressReceived")
          events.toList.map(_.name) should contain("ShippingAddressReceived")
        }
      }
    }

    it("Baker.getAllRecipeInstancesMetadata") {
      test { (client, stateNode, interactionNode, _) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          clientMetadata <- client.getAllRecipeInstancesMetadata
          serverMetadata <- stateNode.getAllRecipeInstancesMetadata
        } yield clientMetadata shouldBe serverMetadata
      }
    }

    it("Baker.getVisualState") {
      test { (client, stateNode, interactionNode, _) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          clientState <- client.getVisualState(recipeInstanceId)
          serverState <- stateNode.getVisualState(recipeInstanceId)
        } yield clientState shouldBe serverState
      }
    }

    it("Baker.retryInteraction") {
      test { (client, _, interactionNode, eventListenerNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        for {
          compiledRecipe <- setupFailingOnceReserveItems(interactionNode)
          events <- setupEventListener(compiledRecipe, eventListenerNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          _ <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          state1 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
          _ <- client.retryInteraction(recipeInstanceId, "ReserveItems")
          state2 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
        } yield {
          state1 should contain("OrderPlaced")
          state1 should not contain("ItemsReserved")
          state2 should contain("OrderPlaced")
          state2 should contain("ItemsReserved")
          events.toList.map(_.name) should contain("OrderPlaced")
          events.toList.map(_.name) should contain("ItemsReserved")
        }
      }
    }

    it("Baker.resolveInteraction") {
      test { (client, _, interactionNode, eventListenerNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        val resolutionEvent = EventInstance.unsafeFrom(
          ItemsReserved(reservedItems = ReservedItems(items = List(Item("item1")), data = Array.empty))
        )
        for {
          compiledRecipe <- setupFailingOnceReserveItems(interactionNode)
          events <- setupEventListener(compiledRecipe, eventListenerNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          _ <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          state1 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
          _ <- client.resolveInteraction(recipeInstanceId, "ReserveItems", resolutionEvent)
          state2data <- client.getRecipeInstanceState(recipeInstanceId)
          state2 = state2data.events.map(_.name)
          eventState = state2data.ingredients.get("reservedItems").map(_.as[ReservedItems].items.head.itemId)
        } yield {
          state1 should contain("OrderPlaced")
          state1 should not contain("ItemsReserved")
          state2 should contain("OrderPlaced")
          state2 should contain("ItemsReserved")
          eventState shouldBe Some("item1")
          events.toList.map(_.name) should contain("OrderPlaced")
          events.toList.map(_.name) should not contain("ItemsReserved") // Manually resolving an interaction does not fire the event to the listeners?
        }
      }
    }

    it("Baker.stopRetryingInteraction") {
      test { (client, _, interactionNode, eventListenerNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        for {
          compiledRecipe <- setupFailingWithRetryReserveItems(interactionNode)
          events <- setupEventListener(compiledRecipe, eventListenerNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          _ <- client.fireEventAndResolveWhenReceived(recipeInstanceId, event)
          state1 <- client.getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))
          _ <- client.stopRetryingInteraction(recipeInstanceId, "ReserveItems")
          state2data <- client.getRecipeInstanceState(recipeInstanceId)
          state2 = state2data.events.map(_.name)
        } yield {
          state1 should contain("OrderPlaced")
          state1 should not contain("ItemsReserved")
          state2 should contain("OrderPlaced")
          state2 should not contain("ItemsReserved")
          events.toList.map(_.name) should contain("OrderPlaced")
          events.toList.map(_.name) should not contain("ItemsReserved")
        }
      }
    }
  }
}

object BaaSIntegrationSpec {

  def setupHappyPath(interactionNode: RemoteInteraction)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new ReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    for {
      _ <- Future { interactionNode.load(makePaymentInstance, reserveItemsInstance, shipItemsInstance) }
    } yield compiledRecipe
  }

  def setupFailingOnceReserveItems(interactionNode: RemoteInteraction)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new FailingOnceReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipeWithBlockingStrategy)
    for {
      _ <- Future { interactionNode.load(makePaymentInstance, reserveItemsInstance, shipItemsInstance) }
    } yield compiledRecipe
  }

  def setupFailingWithRetryReserveItems(interactionNode: RemoteInteraction)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new FailingReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    for {
      _ <- Future { interactionNode.load(makePaymentInstance, reserveItemsInstance, shipItemsInstance) }
    } yield compiledRecipe
  }

  def setupEventListener(recipe: CompiledRecipe, eventListenerNode: RemoteEventListener)(implicit ec: ExecutionContext): Future[mutable.MutableList[EventInstance]] = {
    val buffer = mutable.MutableList.empty[EventInstance]
    eventListenerNode.registerEventListener(recipe.name, (_, event) => {
      buffer.+=(event)
    }).map(_ => buffer)
  }

  type IntegrationTest = ((ScalaBaker, ScalaBaker, RemoteInteraction, RemoteEventListener) => Future[Assertion]) => Future[Assertion]

  type WithOpenPort[A] = StateT[Future, Stream[Int], A]

  def testWith[F[_], Lang <: LanguageApi]
      (test: (ScalaBaker, ScalaBaker, RemoteInteraction, RemoteEventListener) => Future[Assertion])
      (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "BaaSIntegrationSpec-" + testId
    val allPorts: Stream[Int] = Stream.from(50000, 1)
    val program = for {
      clusterTuple <- buildClusterActorSystem(systemName, seedPortCandidate = 0)
      (stateNodeSystem, serverConfig) = clusterTuple
      materializer = ActorMaterializer()(stateNodeSystem)
      stateNodeBaker = AkkaBaker(serverConfig, stateNodeSystem)
      httpPortAndBinding <- runStateNodeHttpServer(stateNodeBaker, stateNodeSystem, materializer)
      (httpPort, httpServerBinding) = httpPortAndBinding
      clientBaker = BakerClient.build(s"http://localhost:$httpPort/", Encryption.NoEncryption)(stateNodeSystem, materializer)
      interactionNode = RemoteInteraction(stateNodeSystem)
      eventListenerNode = RemoteEventListener(stateNodeSystem)
      a <- liftF(test(clientBaker, stateNodeBaker, interactionNode, eventListenerNode))
      _ <- liftF(httpServerBinding.unbind())
      _ <- liftF(stateNodeBaker.gracefulShutdown())
    } yield a
    program.run(allPorts).map(_._2)
  }

  private def buildClusterActorSystem(systemName: String, seedPortCandidate: Int)(implicit ec: ExecutionContext): WithOpenPort[(ActorSystem, Config)] =
    withOpenPort { port =>
      val config = genClusterConfig(systemName, port, seedPortCandidate)
      Future { (ActorSystem(systemName, config), config) }
    }

  private def runStateNodeHttpServer(stateNodeBaker: ScalaBaker, stateNodeSystem: ActorSystem, materializer: Materializer)(implicit ec: ExecutionContext): WithOpenPort[(Int, Http.ServerBinding)] =
    withOpenPort(port => BaaSServer.run(stateNodeBaker, "localhost", port)(stateNodeSystem, materializer).map(port -> _))

  private def withOpenPort[T](f: Int => Future[T])(implicit ec: ExecutionContext): WithOpenPort[T] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], T)] =
      ports match {
        case #::(port, tail) => f(port).map(tail -> _).recoverWith {
          case _: java.net.BindException => search(tail)
          case _: ChannelException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search)
  }

  private def liftF[A](fa: Future[A])(implicit ec: ExecutionContext): WithOpenPort[A] =
    StateT.liftF[Future, Stream[Int], A](fa)

  private def genClusterConfig(systemName: String, port: Int, seedPortCandidate: Int): Config = {
    val seedPort: Int = if(seedPortCandidate == 0) port else seedPortCandidate
    ConfigFactory.parseString(
      s"""
        |baker {
        |  cluster {
        |    seed-nodes = [
        |      "akka.tcp://"$systemName"@localhost:"$seedPort]
        |  }
        |}
        |
        |akka {
        |
        |  remote {
        |    log-remote-lifecycle-events = off
        |    netty.tcp {
        |      hostname = "localhost"
        |      port = $port
        |    }
        |  }
        |
        |  cluster {
        |
        |    seed-nodes = [
        |      "akka.tcp://"$systemName"@localhost:"$seedPort]
        |
        |    # auto downing is NOT safe for production deployments.
        |    # you may want to use it during development, read more about it in the akka docs.
        |    auto-down-unreachable-after = 10s
        |  }
        |}
        |""".stripMargin).withFallback(ConfigFactory.load())
  }
}