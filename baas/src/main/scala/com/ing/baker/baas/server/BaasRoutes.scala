package com.ing.baker.baas.server

import akka.actor.ActorSystem
import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.interaction.client.RemoteInteractionClient
import com.ing.baker.baas.server.protocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl.{ProcessState, RuntimeEvent}
import com.ing.baker.types.Value

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

class BaasRoutes(override val actorSystem: ActorSystem) extends Directives with ClientUtils {

  implicit val timeout: FiniteDuration = 30 seconds
  implicit val ec: ExecutionContext = actorSystem.dispatcher
  implicit val as: ActorSystem = actorSystem

  val defaultEventConfirm = "receive"

  def apply(baker: AkkaBaker): Route = {

    /*
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
      */

    def instanceRoutes(requestId: String) = {
      pathPrefix("event") {
        path("stream") {
          post {
            entity(as[ProcessEventRequest]) { req => complete("Hi") }
          }
        }
      } ~
        path("events") {
          get {
            val processState = baker.getProcessState(requestId)
            complete(processState.map(x => EventsResponse(x.eventNames.map(name => RuntimeEvent(name, Map.empty)))))
          }
        } ~
        path("state") {
          get {
            val events = baker.getProcessState(requestId).map(StateResponse(_))
            complete(events)
          }
        } ~
        path("bake") {
          post {
            entity(as[BakeRequest]) { request =>
              baker.bake(request.recipeId, requestId)
              complete(BakeResponse(new ProcessState("", Map.empty[String, Value], List.empty)))
            }
          }
        } ~
        path("ingredients") {
          get {
            val ingredients = baker.getIngredients(requestId)
            complete(ingredients.map(IngredientsResponse(_)))
          }
        } ~
        path("visual_state") {
          get {
            val visualState = baker.getVisualState(requestId)
            complete(visualState.map(VisualStateResponse(_)))
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
              complete(recipeId.map(AddRecipeResponse(_)))
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
              val interactionImplementation = RemoteInteractionClient(request.name, request.uri, request.inputTypes)
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