package com.ing.baker.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpMethods._
import akka.http.scaladsl.model._
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.baas.ClientUtils._
import com.ing.baker.baas.http.AddInteractionHTTPRequest
import com.ing.baker.recipe.common
import com.ing.baker.runtime.core.{Baker, ProcessState, RuntimeEvent, SensoryEventStatus}
import com.ing.baker.types.{BType, Value}
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

class BAASClient(val host: String, val port: Int)(implicit val actorSystem: ActorSystem) {

  val baseUri = s"http://$host:$port"

  implicit val materializer = ActorMaterializer()

  def logEntity = (entity: ResponseEntity) =>
    entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
      log.info("Got response body: " + body.utf8String)
    }

  val log = LoggerFactory.getLogger(classOf[BAASClient])
  implicit val requestTimeout: FiniteDuration = 30 seconds

  def addRecipe(recipe: common.Recipe) : Unit = {

    val serializedRecipe = BAAS.serializeRecipe(recipe)

    val httpRequest = HttpRequest(
        uri = baseUri +  "/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe))

    doRequest(httpRequest, logEntity)
  }

  def addRemoteImplementation(interactionName: String, uri: String, inputTypes: Seq[BType]) = {

    //Create the request to Add the interaction implmentation to Baas
    log.info("Registering remote implementation client")
    val addInteractionHTTPRequest = AddInteractionHTTPRequest(interactionName, uri, inputTypes)

    val request = HttpRequest(
      uri = s"$baseUri/implementation",
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
        uri = s"$baseUri/$recipeName/$requestId/bake",
        method = POST)

    doRequestAndParseResponse[String](request)
  }

  def getState(recipeName: String, requestId: String): ProcessState = {

    val request = HttpRequest(
        uri = s"$baseUri/$recipeName/$requestId/state",
        method = GET)

    doRequestAndParseResponse[ProcessState](request)
  }

  def getIngredients(recipeName: String, requestId: String): Map[String, Value] = getState(recipeName, requestId).ingredients

  def getVisualState(recipeName: String, requestId: String): String = {

    val request = HttpRequest(
      uri = s"$baseUri/$recipeName/$requestId/visual_state",
      method = GET)

    doRequestAndParseResponse[String](request)
  }

  def getEvents(recipeName: String, requestId: String): List[RuntimeEvent] = {

    val request = HttpRequest(
      uri = s"$baseUri/$recipeName/$requestId/events",
      method = GET)

    doRequestAndParseResponse[List[RuntimeEvent]](request)
  }
}
