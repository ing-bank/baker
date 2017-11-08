package com.ing.baker.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.{HttpMessage, HttpRequest, HttpResponse, StatusCodes}
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.baas.http.AddInteractionHTTPRequest
import com.ing.baker.baas.interaction.http.RemoteInteractionImplementationClient
import com.ing.baker.recipe.common
import com.ing.baker.runtime.core.interations.{InteractionImplementation, MethodInteractionImplementation}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BAASClient(val baseAddress: String, val port: Int) {
  val baseUri = baseAddress + ":" +  port;
  implicit val actorSystem: ActorSystem = ActorSystem("BAASClientActorSystem")
  implicit val materializer = ActorMaterializer()

  def addRecipe(recipe: common.Recipe) : Unit = {
    val serializedRecipe = BAAS.serializeRecipe(recipe)
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  "/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe)))

    val returnMessage: HttpMessage = Await.result(responseFuture, 30 seconds)
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

  var portCounter: Int = 8090
  var hostname: String = "localhost"

  def addImplementation(anyRef: AnyRef): Unit = {
    println("Creating interaction implementation")
    //Create the implementation that is used locally
    val portToUse = portCounter
    portCounter = portCounter + 1

    println("Creating method implementation from Anyref")
    val methodInteractionImplementation: InteractionImplementation = MethodInteractionImplementation.anyRefToInteractionImplementations(anyRef).head

    //Create the locally running interaction implementation
    println("Creating RemoteImplementationClient")
    val remoteInteractionImplementationClient: RemoteInteractionImplementationClient =
      RemoteInteractionImplementationClient(methodInteractionImplementation, hostname, portToUse)

    //start the Remote interaction implementation
    println("Starting RemoteImplementationClient")
    Await.result(remoteInteractionImplementationClient.start(), 10 seconds)

    //Create the request to Add the interaction implmentation to Baas
    println("Registering remote implementation client")
    val addInteractionHTTPRequest: AddInteractionHTTPRequest =
      AddInteractionHTTPRequest(methodInteractionImplementation.name, hostname, portToUse);

    //Send the request to BAAS
    println("Waiting for response from baas")
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  "/implementation",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(kryoPool.toBytesWithClass(addInteractionHTTPRequest))))

    //Handle the response of BAAS
    val returnMessage: HttpMessage = Await.result(responseFuture, 30 seconds)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, headers, entity, _) =>
        entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
          println("Adding interaction succeeded, body: " + body.utf8String)
        }
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        println("Adding interaction failed, response code: " + code)
    }
  }
}
