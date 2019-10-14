package com.ing.baker.runtime.baas.common

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.baas.BaaSServer
import com.ing.baker.runtime.baas.common.CheckoutFlowEvents.ItemsReserved
import com.ing.baker.runtime.baas.common.CheckoutFlowIngredients.{Item, OrderId, ReservedItems, ShippingAddress}
import com.ing.baker.runtime.baas.common.CommonBaaSServerClientSpec.{ClientServerTest, setupFailingOnceReserveItems, setupFailingWithRetryReserveItems, setupHappyPath}
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, Baker => ScalaBaker}
import org.scalatest.compatible.Assertion
import org.scalatest.{AsyncFunSpec, BeforeAndAfterAll, BeforeAndAfterEach, Matchers}

import scala.concurrent.{ExecutionContext, Future}

abstract class CommonBaaSServerClientSpec(clientBaker: (String, ActorSystem, Materializer) => ScalaBaker)
  extends AsyncFunSpec
    with Matchers
    with BeforeAndAfterAll
    with BeforeAndAfterEach {

  val test: ClientServerTest = CommonBaaSServerClientSpec.testWith(clientBaker)

  implicit val timer: Timer[IO] = IO.timer(executionContext)

  describe("Baker Client-Server") {
    it("Baker.addRecipe") {
      test { (client, server) =>
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- server.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.addRecipe (fail with ImplementationsException)") {
      test { (client, _) =>
        val badRecipe = Recipe("BadRecipe")
          .withInteraction(CheckoutFlowInteractions.ShipItemsInteraction)
        val expectedException =
          BakerException.ImplementationsException("No implementation provided for interaction: ShipItems")
        val compiledRecipe = RecipeCompiler
          .compileRecipe(badRecipe)
        for {
          e <- client.addRecipe(compiledRecipe)
              .map(_ => None)
              .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(expectedException)
      }
    }

    it("Baker.getRecipe") {
      test { (client, server) =>
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- client.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getRecipe (fail with NoSuchRecipeException)") {
      test { (client, _) =>
        for {
          e <- client
            .getRecipe("non-existent")
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
      }
    }

    it("Baker.getAllRecipes") {
      test { (client, server) =>
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          recipes <- client.getAllRecipes
        } yield recipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(compiledRecipe)
      }
    }

    it("Baker.bake") {
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          state <- server.getRecipeInstanceState(recipeInstanceId)
        } yield state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    it("Baker.bake (fail with ProcessAlreadyExistsException)") {
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(server)
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
      test { (client, _) =>
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
      test { (_, server) =>
        for {
          e <- server
            .getRecipeInstanceState("non-existent")
            .map(_ => None)
            .recover { case e: BakerException => Some(e) }
        } yield e shouldBe Some(BakerException.NoSuchProcessException("non-existent"))
      }
    }

    it("Baker.fireEventAndResolveWhenReceived") {
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          status <- client.fireEventAndResolveWhenReceived(recipeInstanceId, event)
        } yield status shouldBe SensoryEventStatus.Received
      }
    }

    it("Baker.fireEventAndResolveWhenCompleted") {
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(server)
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
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance("non-existent", Map.empty)
        for {
          compiledRecipe <- setupHappyPath(server)
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
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          compiledRecipe <- setupHappyPath(server)
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
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          clientMetadata <- client.getAllRecipeInstancesMetadata
          serverMetadata <- server.getAllRecipeInstancesMetadata
        } yield clientMetadata shouldBe serverMetadata
      }
    }

    it("Baker.getVisualState") {
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          compiledRecipe <- setupHappyPath(server)
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          clientState <- client.getVisualState(recipeInstanceId)
          serverState <- server.getVisualState(recipeInstanceId)
        } yield clientState shouldBe serverState
      }
    }

    it("Baker.retryInteraction") {
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        for {
          compiledRecipe <- setupFailingOnceReserveItems(server)
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
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        val resolutionEvent = EventInstance.unsafeFrom(
          ItemsReserved(reservedItems = ReservedItems(items = List(Item("item1")), data = Array.empty))
        )
        for {
          compiledRecipe <- setupFailingOnceReserveItems(server)
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
      test { (client, server) =>
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.OrderPlaced(orderId = OrderId("order1"), List.empty))
        for {
          compiledRecipe <- setupFailingWithRetryReserveItems(server)
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

object CommonBaaSServerClientSpec {

  def setupHappyPath(serverBaker: ScalaBaker)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new ReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    for {
      _ <- serverBaker.addInteractionInstances(Seq(makePaymentInstance, reserveItemsInstance, shipItemsInstance))
    } yield compiledRecipe
  }

  def setupFailingOnceReserveItems(serverBaker: ScalaBaker)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new FailingOnceReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipeWithBlockingStrategy)
    for {
      _ <- serverBaker.addInteractionInstances(Seq(makePaymentInstance, reserveItemsInstance, shipItemsInstance))
    } yield compiledRecipe
  }

  def setupFailingWithRetryReserveItems(serverBaker: ScalaBaker)(implicit ec: ExecutionContext, timer: Timer[IO]): Future[CompiledRecipe] = {
    val makePaymentInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance = InteractionInstance.unsafeFrom(new FailingReserveItemsInstance())
    val shipItemsInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    for {
      _ <- serverBaker.addInteractionInstances(Seq(makePaymentInstance, reserveItemsInstance, shipItemsInstance))
    } yield compiledRecipe
  }

  type ClientServerTest = ((ScalaBaker, ScalaBaker) => Future[Assertion]) => Future[Assertion]

  val allPorts: Stream[Int] = Stream.from(50000, 1)

  def testWith[F[_], Lang <: LanguageApi]
      (clientBaker: (String, ActorSystem, Materializer) => ScalaBaker)
      (t: (ScalaBaker, ScalaBaker) => Future[Assertion])
      (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    implicit val system: ActorSystem = ActorSystem("ScalaDSLBaaSServerClientSpec-" + testId)
    implicit val materializer: Materializer = ActorMaterializer()
    val host: String = "localhost"
    val serverBaker = ScalaBaker.akkaLocalDefault(system, materializer)
    for {
      (client, shutdown) <- buildFromStream(allPorts, { port: Int =>
        val client = clientBaker(s"http://$host:$port/", system, materializer)
        val shutdown = BaaSServer.run(serverBaker, host, port)
        shutdown.map(s => (client, s))
      })
      a <- t(client, serverBaker)
      _ <- shutdown.unbind()
      _ <- serverBaker.gracefulShutdown()
    } yield a
  }

  private def buildFromStream[S, T](ports: Stream[S], f: S => Future[T])(implicit ec: ExecutionContext): Future[T] =
    ports match {
      case #::(port, tail) => f(port).recoverWith {
        case _: java.net.BindException => buildFromStream(tail, f)
      }
    }
}