package com.ing.baker.runtime.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import akka.stream.Materializer
import com.ing.baker.runtime.akka.actor.serialization.{Encryption, SerializersProvider}
import com.ing.baker.runtime.baas.BaaSProto._
import com.ing.baker.runtime.baas.MarshallingUtils._
import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.Future

object BaaSServer {

  def run(baker: Baker, host: String, port: Int)(implicit system: ActorSystem, mat: Materializer): Future[Http.ServerBinding] = {
    val encryption = Encryption.NoEncryption
    val server = new BaaSServer()(system, mat, baker, encryption)
    Http().bindAndHandle(server.route, host, port)
  }
}

class BaaSServer(implicit system: ActorSystem, mat: Materializer, baker: Baker, encryption: Encryption) {

  import system.dispatcher

  implicit val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  def route: Route = pathPrefix("api" / "v3")(concat(addRecipe, getRecipe))

  def addRecipe: Route = post(path("addRecipe") {
    entity(as[BaaSProtocol.AddRecipeRequest]) { request =>
      complete(baker.addRecipe(request.compiledRecipe).map(BaaSProtocol.AddRecipeResponse))
    }
  })

  def getRecipe: Route = post(path("getRecipe") {
    entity(as[BaaSProtocol.GetRecipeRequest]) { request =>
      complete(baker.getRecipe(request.recipeId).map(BaaSProtocol.GetRecipeResponse))
    }
  })
}
