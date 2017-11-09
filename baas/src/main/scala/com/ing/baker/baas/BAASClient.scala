package com.ing.baker.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.HttpMethods._
import akka.http.scaladsl.model._
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.baas.http._
import com.ing.baker.baas.interaction.http.RemoteInteractionImplementationAPI
import com.ing.baker.recipe.common
import com.ing.baker.runtime.core.interations.{InteractionImplementation, MethodInteractionImplementation}
import com.ing.baker.runtime.core.{Baker, SensoryEventStatus}
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BAASClient(val host: String, val port: Int) {

  val baseUri = s"http://$host:$port"

  implicit val actorSystem: ActorSystem = ActorSystem("BAASClientActorSystem")
  implicit val materializer = ActorMaterializer()

  val log = LoggerFactory.getLogger(classOf[BAASClient])
  val requestTimeout = 30 seconds

  def entityFromResponse[T](entity: ResponseEntity): T = {
    val byteString = Await.result(entity.dataBytes.runFold(ByteString(""))(_ ++ _), requestTimeout)
    kryoPool.fromBytes(byteString.toArray).asInstanceOf[T]
  }

  def addRecipe(recipe: common.Recipe) : Unit = {
    val serializedRecipe = BAAS.serializeRecipe(recipe)
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  "/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe)))

    val returnMessage: HttpMessage = Await.result(responseFuture, requestTimeout)

    returnMessage match {
      case HttpResponse(StatusCodes.OK, headers, entity, _) =>
        entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
          log.info("Got response, body: " + body.utf8String)
        }
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Add recipe failed, response code: " + code)
        throw new RuntimeException("Adding interaction failed")
    }
  }

  var portCounter: Int = 8090
  var hostname: String = "localhost"

  def addImplementation(anyRef: AnyRef): Unit = {
    log.info("Creating interaction implementation")
    //Create the implementation that is used locally

    log.info("Creating method implementation from Anyref")
    val methodInteractionImplementations: Seq[InteractionImplementation] =
      MethodInteractionImplementation.anyRefToInteractionImplementations(anyRef)

    methodInteractionImplementations.foreach{ im =>
      val portToUse = portCounter
      portCounter = portCounter + 1
      createRemoteForImplementation(im, portToUse)
    }
  }

  private def createRemoteForImplementation(interactionImplementation: InteractionImplementation, portToUse: Int): Unit = {
    //Create the locally running interaction implementation
    log.info("Creating RemoteImplementationClient")
    val remoteInteractionImplementationClient: RemoteInteractionImplementationAPI =
      RemoteInteractionImplementationAPI(interactionImplementation, hostname, portToUse)

    //start the Remote interaction implementation
    log.info("Starting RemoteImplementationClient")
    Await.result(remoteInteractionImplementationClient.start(), 10 seconds)

    //Create the request to Add the interaction implmentation to Baas
    log.info("Registering remote implementation client")
    val addInteractionHTTPRequest: AddInteractionHTTPRequest =
      AddInteractionHTTPRequest(interactionImplementation.name, hostname, portToUse);

    //Send the request to BAAS
    log.info("Sending request to baas")
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  "/implementation",
        method = POST,
        entity = ByteString.fromArray(kryoPool.toBytesWithClass(addInteractionHTTPRequest))))

    //Handle the response of BAAS
    log.info("Waiting for response from baas")
    val returnMessage: HttpMessage = Await.result(responseFuture, requestTimeout)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
          log.info("Adding interaction succeeded, body: " + body.utf8String)
        }
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Adding interaction failed, response code: " + code)
        throw new RuntimeException
    }
  }

  def handleEvent(recipeName: String, requestId: String, event: Any): SensoryEventStatus = {
    //Create request to give to Baker
    log.info("Creating runtime event to fire")
    val runtimeEvent = Baker.eventExtractor.extractEvent(event)

    //Send the request to BAAS
    log.info("Sending handle event request to BAAS")
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri =  s"$baseUri/$recipeName/$requestId/bake",
        method = POST))

    //Handle the response from BAAS
    log.info("Waiting for response from baas")
    val returnMessage: HttpMessage = Await.result(responseFuture, requestTimeout)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        val response = entityFromResponse[HandleEventHTTPResponse](entity)
        response.sensoryEventStatus
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Adding interaction failed, response code: " + code)
        throw new RuntimeException
    }
  }

  def bake(recipeName: String, requestId: String): Unit = {

    //Send the request to BAAS
    log.info("Sending bake request to BAAS")
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  s"/$recipeName/$requestId/bake",
        method = POST))

    //Handle the response from BAAS
    log.info("Waiting for response from baas")
    val returnMessage: HttpMessage = Await.result(responseFuture, requestTimeout)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        val response = entityFromResponse[BakeHTTPResponse](entity)
        log.info(response.toString)
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Baking failed, response code: " + code)
        throw new RuntimeException
    }
  }

  def getState(recipeName: String, requestId: String): GetStateHTTResponse = {
    //Send the request to BAAS
    log.info("Sending bake request to BAAS")
    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = baseUri +  s"/$recipeName/$requestId/state",
        method = GET))

    //Handle the response from BAAS
    log.info("Waiting for response from baas")
    val returnMessage: HttpMessage = Await.result(responseFuture, requestTimeout)

    returnMessage match {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        val response = entityFromResponse[GetStateHTTResponse](entity)
        log.info(response.toString)
        response
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Getting state failed, response code: " + code)
        throw new RuntimeException("Getting state failed")
    }
  }
}
