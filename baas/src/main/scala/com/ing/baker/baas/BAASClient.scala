package com.ing.baker.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpMethods._
import akka.http.scaladsl.model._
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.baas.KryoUtil.defaultKryoPool
import com.ing.baker.baas.ClientUtils._
import com.ing.baker.baas.http.AddInteractionHTTPRequest
import com.ing.baker.recipe.common
import com.ing.baker.runtime.core.{Baker, ProcessState, RuntimeEvent, SensoryEventStatus}
import com.ing.baker.types.{Type, Value}
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

  def addRecipe(recipe: common.Recipe) : String = {

    val serializedRecipe = KryoUtil.serialize(recipe)

    val httpRequest = HttpRequest(
        uri = baseUri +  "/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe))

    doRequestAndParseResponse[String](httpRequest)
  }

  def addRemoteImplementation(interactionName: String, uri: String, inputTypes: Seq[Type]) = {

    //Create the request to Add the interaction implmentation to Baas
    log.info("Registering remote implementation client")
    val addInteractionHTTPRequest = AddInteractionHTTPRequest(interactionName, uri, inputTypes)

    val request = HttpRequest(
      uri = s"$baseUri/implementation",
      method = POST,
      entity = ByteString.fromArray(defaultKryoPool.toBytesWithClass(addInteractionHTTPRequest)))

    doRequest(request, logEntity)
  }

  def processEvent(requestId: String, event: Any, confirmation: EventConfirmation): SensoryEventStatus = {

    //Create request to give to Baker
    log.info("Creating runtime event to fire")
    val runtimeEvent = Baker.extractEvent(event)

    val request = HttpRequest(
        uri =  s"$baseUri/$requestId/event?confirm=${confirmation.name}",
        method = POST,
        entity = ByteString.fromArray(defaultKryoPool.toBytesWithClass(runtimeEvent)))

    doRequestAndParseResponse[SensoryEventStatus](request)
  }

  def bake(recipeId: String, requestId: String): Unit = {

    val request = HttpRequest(
        uri = s"$baseUri/$requestId/$recipeId/bake",
        method = POST)

    doRequestAndParseResponse[String](request)
  }

  def getState(requestId: String): ProcessState = {

    val request = HttpRequest(
        uri = s"$baseUri/$requestId/state",
        method = GET)

    doRequestAndParseResponse[ProcessState](request)
  }

  def getIngredients(requestId: String): Map[String, Value] = getState(requestId).ingredients

  def getVisualState(requestId: String): String = {

    val request = HttpRequest(
      uri = s"$baseUri/$requestId/visual_state",
      method = GET)

    doRequestAndParseResponse[String](request)
  }

  def getEvents(requestId: String): List[RuntimeEvent] = {

    val request = HttpRequest(
      uri = s"$baseUri/$requestId/events",
      method = GET)

    doRequestAndParseResponse[List[RuntimeEvent]](request)
  }
}
