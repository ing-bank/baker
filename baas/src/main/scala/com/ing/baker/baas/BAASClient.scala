package com.ing.baker.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.{HttpMessage, HttpRequest, HttpResponse, StatusCodes}
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.recipe.common
import scala.concurrent.ExecutionContext.Implicits.global

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BAASClient(val baseAddress: String, val port: Int) {
  val baseUri = baseAddress + port;
  implicit val actorSystem: ActorSystem = ActorSystem("BAASUserManagerActorSystem")
  implicit val materializer = ActorMaterializer()

  def addRecipe(recipe: common.Recipe) : Unit = {
    val serializedRecipe = BAAS.serializeRecipe(recipe)
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  "/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe)))

    val returnMessage: HttpMessage = Await.result(responseFuture, 10 seconds)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, headers, entity, _) =>
        entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
          println("Got response, body: " + body.utf8String)
        }
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        println("Request failed, response code: " + code)
    }
  }
}
