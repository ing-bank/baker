package com.ing.baker.baas.server

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpEntity.CloseDelimited
import akka.http.scaladsl.model.{ContentTypes, HttpResponse, StatusCodes}
import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.interaction.client.RemoteInteractionClient
import com.ing.baker.baas.server.protocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.runtime.core.{AkkaBaker, Baker, BakerResponseEventProtocol, ProcessState, RuntimeEvent}

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._

class BaasRoutes(override val actorSystem: ActorSystem) extends Directives with ClientUtils {

  implicit val timeout: FiniteDuration = 30 seconds
  implicit val ec: ExecutionContext = actorSystem.dispatcher

  val defaultEventConfirm = "receive"

  def apply(baker: AkkaBaker): Route = {

    def streamBakerResponse(requestId: String, event: RuntimeEvent): HttpResponse =
      HttpResponse(
        status = StatusCodes.OK,
        entity = CloseDelimited(
          contentType = ContentTypes.`application/octet-stream`,
          data = baker.processEventStream(requestId, event)
            .via(serializeFlow[BakerResponseEventProtocol])
            .map(_ ++ BakerResponseEventProtocol.SerializationDelimiter)
        )
      )

    def instanceRoutes(requestId: String) = {
      pathPrefix("event") {
        path("stream") {
          post {
            entity(as[ProcessEventRequest]) { req => complete(streamBakerResponse(requestId, req.event)) }
          }
        } ~
        post {
          entity(as[ProcessEventRequest]) { request =>
            val sensoryEventStatus = baker.processEvent(requestId, request.event)
            complete(ProcessEventResponse(sensoryEventStatus))
          }
        }
      } ~
        path("events") {
          get {
            val events = baker.events(requestId)
            complete(EventsResponse(events))
          }
        } ~
        path("state") {
          get {
            val events: ProcessState = baker.getProcessState(requestId)
            complete(StateResponse(events))
          }
        } ~
        path("bake") {
          post {
            entity(as[BakeRequest]) { request =>
              val processState = baker.bake(request.recipeId, requestId)
              complete(BakeResponse(processState))
            }
          }
        } ~
        path("ingredients") {
          get {
            val ingredients = baker.getIngredients(requestId)
            complete(IngredientsResponse(ingredients))
          }
        } ~
        path("visual_state") {
          get {
            val visualState = baker.getVisualState(requestId)
            complete(VisualStateResponse(visualState))
          }
        }
    }


    val baasRoutes = {

      path("recipe") {
        post {
          entity(as[AddRecipeRequest]) { case AddRecipeRequest(compiledRecipe) =>
            try {
              println(s"Adding recipe called: ${compiledRecipe.name}")
              val recipeId = baker.addRecipe(compiledRecipe)
              complete(AddRecipeResponse(recipeId))
            } catch {
              case e: Exception => {
                println(s"Exception when adding recipe: ${e.getMessage}")
                throw e
              }
            }
          }
        } ~
        get {
          pathPrefix(Segment) { recipeId =>
            complete(baker.getRecipe(recipeId))
          }
        }
      } ~
        path("implementation") {
          post {
            entity(as[AddInteractionHTTPRequest]) { request =>

              //Create a RemoteInteractionImplementation
              val interactionImplementation = RemoteInteractionClient(request.name, request.uri, request.inputTypes)(actorSystem)
              println(s"Adding interaction called: ${request.name}")

              //Register it to BAAS
              baker.addImplementation(interactionImplementation)

              //return response
              complete(AddInteractionHTTPResponse(
                s"Interaction: ${interactionImplementation.name} added"))
            }
          }
        } ~ pathPrefix(Segment)(instanceRoutes)
    }
    baasRoutes
  }


}