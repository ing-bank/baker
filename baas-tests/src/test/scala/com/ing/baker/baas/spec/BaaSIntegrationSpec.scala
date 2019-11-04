package com.ing.baker.baas.spec

import java.util.UUID

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.baas.recipe.CheckoutFlowEvents.ItemsReserved
import com.ing.baker.baas.recipe.CheckoutFlowIngredients.{Item, OrderId, ReservedItems, ShippingAddress}
import com.ing.baker.baas.recipe._
import com.ing.baker.baas.scaladsl.{BaaSInteractionInstance, BakerClient}
import com.ing.baker.baas.spec.BaaSIntegrationSpec._
import com.ing.baker.baas.state.BaaSServer
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, Baker => ScalaBaker}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.{Config, ConfigFactory}
import org.jboss.netty.channel.ChannelException
import org.scalatest._

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
      test { (client, server, interactionNode) =>
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- server.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getRecipe") {
      test { (client, _, interactionNode) =>
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- client.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getRecipe (fail with NoSuchRecipeException)") {
      test { (client, _, _) =>
        for {
          e <- client
            .getRecipe("non-existent")
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
      }
    }

    it("Baker.getAllRecipes") {
      test { (client, server, interactionNode) =>
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          recipes <- client.getAllRecipes
        } yield recipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(compiledRecipe)
      }
    }

    it("Baker.bake") {
      test { (client, server, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          state <- server.getRecipeInstanceState(recipeInstanceId)
        } yield state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    it("Baker.bake (fail with ProcessAlreadyExistsException)") {
      test { (client, server, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          e <- client
            .bake(recipeId, recipeInstanceId)
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
          state <- server.getRecipeInstanceState(recipeInstanceId)
        } yield {
          e shouldBe Some(BakerException.ProcessAlreadyExistsException(recipeInstanceId))
          state.recipeInstanceId shouldBe recipeInstanceId
        }
      }
    }

    it("Baker.bake (fail with NoSuchRecipeException)") {
      test { (client, _, _) =>
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
      test { (_, server, _) =>
        for {
          e <- server
            .getRecipeInstanceState("non-existent")
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchProcessException("non-existent"))
      }
    }

    it("Baker.fireEventAndResolveWhenReceived") {
      test { (client, server, interactionNode) =>
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
      test { (client, server, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          result <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, event)
          serverState <- server.getRecipeInstanceState(recipeInstanceId)
        } yield {
          result.eventNames should contain("ShippingAddressReceived")
          serverState.events.map(_.name) should contain("ShippingAddressReceived")
        }
      }
    }

    it("Baker.fireEventAndResolveWhenCompleted (fails with IllegalEventException)") {
      test { (client, server, interactionNode) =>
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
          serverState <- server.getRecipeInstanceState(recipeInstanceId)
        } yield {
          result shouldBe Some(BakerException.IllegalEventException("No event with name 'non-existent' found in recipe 'Webshop'"))
          serverState.events.map(_.name) should not contain("ShippingAddressReceived")
        }
      }
    }

    it("Baker.fireEventAndResolveOnEvent") {
      test { (client, server, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          result <- client.fireEventAndResolveOnEvent(recipeInstanceId, event, "ShippingAddressReceived")
          serverState <- server.getRecipeInstanceState(recipeInstanceId)
        } yield {
          result.eventNames should contain("ShippingAddressReceived")
          serverState.events.map(_.name) should contain("ShippingAddressReceived")
        }
      }
    }

    it("Baker.getAllRecipeInstancesMetadata") {
      test { (client, server, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          clientMetadata <- client.getAllRecipeInstancesMetadata
          serverMetadata <- server.getAllRecipeInstancesMetadata
        } yield clientMetadata shouldBe serverMetadata
      }
    }

    it("Baker.getVisualState") {
      test { (client, server, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(interactionNode)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          clientState <- client.getVisualState(recipeInstanceId)
          serverState <- server.getVisualState(recipeInstanceId)
        } yield clientState shouldBe serverState
      }
    }

    it("Baker.retryInteraction") {
      test { (client, _, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        for {
          compiledRecipe <- setupFailingOnceReserveItems(interactionNode)
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
        }
      }
    }

    it("Baker.resolveInteraction") {
      test { (client, _, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        val resolutionEvent = EventInstance.unsafeFrom(
          ItemsReserved(reservedItems = ReservedItems(items = List(Item("item1")), data = Array.empty))
        )
        for {
          compiledRecipe <- setupFailingOnceReserveItems(interactionNode)
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
        }
      }
    }

    it("Baker.stopRetryingInteraction") {
      test { (client, _, interactionNode) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        for {
          compiledRecipe <- setupFailingWithRetryReserveItems(interactionNode)
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
        }
      }
    }
  }
}

object BaaSIntegrationSpec {

  def setupHappyPath(serverBaker: BaaSInteractionInstance)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new ReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    for {
      _ <- Future { serverBaker.load(makePaymentInstance, reserveItemsInstance, shipItemsInstance) }
    } yield compiledRecipe
  }

  def setupFailingOnceReserveItems(serverBaker: BaaSInteractionInstance)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new FailingOnceReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipeWithBlockingStrategy)
    for {
      _ <- Future { serverBaker.load(makePaymentInstance, reserveItemsInstance, shipItemsInstance) }
    } yield compiledRecipe
  }

  def setupFailingWithRetryReserveItems(serverBaker: BaaSInteractionInstance)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new FailingReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    for {
      _ <- Future { serverBaker.load(makePaymentInstance, reserveItemsInstance, shipItemsInstance) }
    } yield compiledRecipe
  }

  type IntegrationTest = ((ScalaBaker, ScalaBaker, BaaSInteractionInstance) => Future[Assertion]) => Future[Assertion]

  type WithOpenPort[A] = StateT[Future, Stream[Int], A]

  def testWith[F[_], Lang <: LanguageApi]
      (test: (ScalaBaker, ScalaBaker, BaaSInteractionInstance) => Future[Assertion])
      (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "ScalaDSLBaaSServerClientSpec-" + testId
    val allPorts: Stream[Int] = Stream.from(50000, 1)
    val program = for {
      clientServerQuadruple <- buildBaaSClientServer(systemName)
      (clientBaker, stateNodeBaker, stateNodePort, httpServerBinding) = clientServerQuadruple
      interactionNodeTriplet <- buildClusterActorSystem(systemName, seedPortCandidate = stateNodePort)
      (interactionNodeSystem, _, _) = interactionNodeTriplet
      interactionNode = BaaSInteractionInstance(interactionNodeSystem)
      a <- liftF(test(clientBaker, stateNodeBaker, interactionNode))
      _ <- liftF(interactionNodeSystem.terminate())
      _ <- liftF(httpServerBinding.unbind())
      _ <- liftF(stateNodeBaker.gracefulShutdown())
    } yield a
    program.run(allPorts).map(_._2)
  }

  private def buildBaaSClientServer
      (systemName: String)
      (implicit ec: ExecutionContext): WithOpenPort[(ScalaBaker, ScalaBaker, Int, Http.ServerBinding)] = {
    for {
      clusterTriplet <- buildClusterActorSystem(systemName, seedPortCandidate = 0)
      (stateNodeSystem, serverConfig, stateNodePort) = clusterTriplet
      materializer = ActorMaterializer()(stateNodeSystem)
      stateNodeBaker = AkkaBaker(serverConfig, stateNodeSystem)
      httpPortAndBinding <- runStateNodeHttpServer(stateNodeBaker, stateNodeSystem, materializer)
      (httpPort, httpServerBinding) = httpPortAndBinding
      clientBaker = BakerClient.build(s"http://localhost:$httpPort/", Encryption.NoEncryption)(stateNodeSystem, materializer)
    } yield (clientBaker, stateNodeBaker, stateNodePort, httpServerBinding)
  }

  private def buildClusterActorSystem(systemName: String, seedPortCandidate: Int)(implicit ec: ExecutionContext): WithOpenPort[(ActorSystem, Config, Int)] =
    withOpenPort { port =>
      val config = genClusterConfig(systemName, port, seedPortCandidate)
      Future { (ActorSystem(systemName, config), config, port) }
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