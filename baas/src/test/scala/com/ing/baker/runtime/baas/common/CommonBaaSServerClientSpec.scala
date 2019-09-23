package com.ing.baker.runtime.baas.common

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.stream.Materializer
import cats.effect.{IO, Timer}
import cats.~>
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.baas.BaaSServer
import com.ing.baker.runtime.common.Baker
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl.{InteractionInstance, Baker => ScalaBaker}
import org.scalatest.{AsyncFunSpec, BeforeAndAfterAll, Matchers}

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

abstract class CommonBaaSServerClientSpec[F[_]](
                                                 clientBaker: Baker[F],
                                                 serverBaker: ScalaBaker,
                                                 host: String,
                                                 port: Int,
                                                 toFuture: F ~> Future)(
                                                 implicit system: ActorSystem, materializer: Materializer
                                               )
  extends AsyncFunSpec
    with Matchers
    with BeforeAndAfterAll
    with LanguageApi {

  var serverShutdown: Http.ServerBinding = _

  implicit val timer: Timer[IO] = IO.timer(system.dispatcher)

  override def beforeAll(): Unit = {
    val makePaymentInstance: InteractionInstance = InteractionInstance.unsafeFrom(new MakePaymentInstance())
    val reserveItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(new ReserveItemsInstance())
    val shipItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(new ShipItemsInstance())
    val addInteractions = serverBaker.addInteractionInstances(Seq(makePaymentInstance, reserveItemsInstance, shipItemsInstance))
    Await.result(addInteractions, 10 seconds)
    serverShutdown = Await.result(BaaSServer.run(serverBaker, host, port), 10 seconds)
  }

  override def afterAll(): Unit = {
    Await.result(serverShutdown.unbind(), 10 seconds)
  }

  describe("Baker Client-Server comm") {
    it("Baker.addRecipe") {
      val compiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
      for {
        recipeId <- toFuture(clientBaker.addRecipe(compiledRecipe))
        recipeInformation <- serverBaker.getRecipe(recipeId)
      } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
    }
  }
}
