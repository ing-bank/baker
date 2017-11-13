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
import com.ing.baker.runtime.core.{Baker, ProcessState, SensoryEventStatus}
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BAASClient(val host: String, val port: Int)(implicit val actorSystem: ActorSystem) {

  val baseUri = s"http://$host:$port"

  implicit val materializer = ActorMaterializer()

  val log = LoggerFactory.getLogger(classOf[BAASClient])
  val requestTimeout = 30 seconds

  def entityFromResponse[T](entity: ResponseEntity): T = {
    val byteString = Await.result(entity.dataBytes.runFold(ByteString(""))(_ ++ _), requestTimeout)
    kryoPool.fromBytes(byteString.toArray).asInstanceOf[T]
  }

  def logEntity = (entity: ResponseEntity) =>
    entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
      log.info("Got response body: " + body.utf8String)
    }

  def doRequestAndParseResponse[T](httpRequest: HttpRequest): T = {

    doRequest(httpRequest, e => entityFromResponse[T](e))
  }

  def doRequest[T](httpRequest: HttpRequest, fn: ResponseEntity => T): T = {

    log.info(s"Sending request: $httpRequest")

    val response: HttpMessage = Await.result(Http().singleRequest(httpRequest), requestTimeout)

    response match {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        fn(entity)
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Request failed with response code: " + code)
        throw new RuntimeException("Request failed with response code: " + code)
    }
  }

  def addRecipe(recipe: common.Recipe) : Unit = {

    val serializedRecipe = BAAS.serializeRecipe(recipe)

    val httpRequest = HttpRequest(
        uri = baseUri +  "/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe))

    doRequest(httpRequest, logEntity)
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
      AddInteractionHTTPRequest(interactionImplementation.name, hostname, portToUse)

    val request = HttpRequest(
        uri = baseUri +  "/implementation",
        method = POST,
        entity = ByteString.fromArray(kryoPool.toBytesWithClass(addInteractionHTTPRequest)))

    doRequest(request, logEntity)
  }

  def handleEvent(recipeName: String, requestId: String, event: Any, confirmation: EventConfirmation): SensoryEventStatus = {

    //Create request to give to Baker
    log.info("Creating runtime event to fire")
    val runtimeEvent = Baker.eventExtractor.extractEvent(event)

    val request = HttpRequest(
        uri =  s"$baseUri/$recipeName/$requestId/event?confirm=${confirmation.name}",
        method = POST,
        entity = ByteString.fromArray(kryoPool.toBytesWithClass(runtimeEvent)))

    doRequestAndParseResponse[SensoryEventStatus](request)
  }

  def bake(recipeName: String, requestId: String): Unit = {

    val request = HttpRequest(
        uri = baseUri +  s"/$recipeName/$requestId/bake",
        method = POST)

    doRequestAndParseResponse[ProcessState](request)
  }

  def getState(recipeName: String, requestId: String): ProcessState = {

    val request = HttpRequest(
        uri = baseUri +  s"/$recipeName/$requestId/state",
        method = GET)

    doRequestAndParseResponse[ProcessState](request)
  }

  def getVisualState(recipeName: String, requestId: String): String = {

    val request = HttpRequest(
      uri = baseUri +  s"/$recipeName/$requestId/visual_state",
      method = GET)

    doRequestAndParseResponse[String](request)
  }
}
