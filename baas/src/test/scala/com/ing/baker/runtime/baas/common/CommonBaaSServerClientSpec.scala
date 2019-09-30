package com.ing.baker.runtime.baas.common

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.baas.BaaSServer
import com.ing.baker.runtime.baas.common.CheckoutFlowIngredients.ShippingAddress
import com.ing.baker.runtime.baas.common.CommonBaaSServerClientSpec.ClientServerTest
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, Baker => ScalaBaker}
import org.scalatest.compatible.Assertion
import org.scalatest.{AsyncFunSpec, BeforeAndAfterAll, BeforeAndAfterEach, Matchers}

import scala.concurrent.{ExecutionContext, Future}

abstract class CommonBaaSServerClientSpec(clientBaker: (String, ActorSystem, Materializer) => ScalaBaker)
  extends AsyncFunSpec
    with Matchers
    with BeforeAndAfterAll
    with BeforeAndAfterEach
    with LanguageApi {

  val test: ClientServerTest = CommonBaaSServerClientSpec.testWith(clientBaker)

  describe("Baker Client-Server") {
    it("Baker.addRecipe") {
      test { (client, server) =>
        val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
        for {
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- server.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getRecipe") {
      test { (client, _) =>
        val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
        for {
          recipeId <- client.addRecipe(compiledRecipe)
          recipeInformation <- client.getRecipe(recipeId)
        } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
      }
    }

    it("Baker.getAllRecipes") {
      test { (client, _) =>
        val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
        for {
          recipeId <- client.addRecipe(compiledRecipe)
          recipes <- client.getAllRecipes
        } yield recipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(compiledRecipe)
      }
    }

    it("Baker.bake") {
      test { (client, server) =>
        val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
        val recipeInstanceId: String = UUID.randomUUID().toString
        for {
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          state <- server.getRecipeInstanceState(recipeInstanceId)
        } yield state.recipeInstanceId shouldBe recipeInstanceId
      }
    }

    it("Baker.fireEventAndResolveWhenReceived") {
      test { (client, server) =>
        val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          status <- client.fireEventAndResolveWhenReceived(recipeInstanceId, event)
        } yield status shouldBe SensoryEventStatus.Received
      }
    }

    it("Baker.fireEventAndResolveWhenCompleted") {
      test { (client, server) =>
        val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
        val recipeInstanceId: String = UUID.randomUUID().toString
        val event = EventInstance.unsafeFrom(
          CheckoutFlowEvents.ShippingAddressReceived(ShippingAddress("address")))
        for {
          recipeId <- client.addRecipe(compiledRecipe)
          _ <- client.bake(recipeId, recipeInstanceId)
          result <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, event)
        } yield result.eventNames should contain("ShippingAddressReceived")
      }
    }
  }
}

object CommonBaaSServerClientSpec {

  type ClientServerTest = ((ScalaBaker, ScalaBaker) => Future[Assertion]) => Future[Assertion]

  val allPorts: Stream[Int] = Stream.from(50000, 1)

  def testWith[F[_], Lang <: LanguageApi]
      (clientBaker: (String, ActorSystem, Materializer) => ScalaBaker)
      (t: (ScalaBaker, ScalaBaker) => Future[Assertion])
      (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    implicit val system: ActorSystem = ActorSystem("ScalaDSLBaaSServerClientSpec-" + testId)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val timer: Timer[IO] = IO.timer(system.dispatcher)
    val host: String = "localhost"
    val serverBaker = ScalaBaker.akkaLocalDefault(system, materializer)
    val makePaymentInstance: InteractionInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(new ReserveItemsInstance())
    val shipItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    for {
      _ <- serverBaker.addInteractionInstances(Seq(makePaymentInstance, reserveItemsInstance, shipItemsInstance))
      (client, shutdown) <- createClientServerPair(allPorts, { port =>
        val client = clientBaker(s"http://$host:$port/", system, materializer)
        val shutdown = BaaSServer.run(serverBaker, host, port)
        shutdown.map(s => (client, s))
      })
      a <- t(client, serverBaker)
      _ <- shutdown.unbind()
      _ <- serverBaker.gracefulShutdown()
    } yield a
  }

  private def createClientServerPair[T](ports: Stream[Int], buildServer: Int => Future[T])(implicit ec: ExecutionContext): Future[T] =
    ports match {
      case #::(port, tail) => buildServer(port).recoverWith {
        case _: java.net.BindException => createClientServerPair(tail, buildServer)
      }
    }
}