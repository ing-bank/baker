package com.ing.baker.baas.server

import akka.actor.ActorSystem
import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.server.protocol.BaasServerProtocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.core.{Baker, ProcessState, RuntimeEvent}
import com.ing.baker.baas.interaction.client.RemoteInteractionClient

import scala.concurrent.duration._

class BaasRoutes(override val actorSystem: ActorSystem) extends Directives with ClientUtils {

  implicit val timeout: FiniteDuration = 30 seconds

  val defaultEventConfirm = "receive"

  def apply(baker: Baker): Route = {

    def instanceRoutes(requestId: String) = {
      path("event") {
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
        path( "bake") {
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
        } ~ pathPrefix(Segment) {
        instanceRoutes _
      }
    }
    baasRoutes
  }


}