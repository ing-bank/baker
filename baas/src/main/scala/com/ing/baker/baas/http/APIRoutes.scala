package com.ing.baker.baas.http

import akka.actor.ActorSystem
import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.interaction.RemoteInteractionClient
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.commonserialize
import com.ing.baker.runtime.core.{Baker, RuntimeEvent}

import scala.concurrent.duration._

object APIRoutes extends Directives with BaasMarshalling {

  implicit val timeout: FiniteDuration = 30 seconds

  val defaultEventConfirm = "receive"

  def apply(baker: Baker)(implicit actorSystem: ActorSystem): Route = {

    def recipeRoutes(requestId: String) = {

      path("event") {
        post {
          (entity(as[RuntimeEvent]) & parameter('confirm.as[String] ?)) { (event, confirm) =>

            val sensoryEventStatus = confirm.getOrElse(defaultEventConfirm) match {
              case "received"  => baker.processEventAsync(requestId, event).confirmReceived()
              case "completed" => baker.processEventAsync(requestId, event).confirmCompleted()
              case other      => throw new IllegalArgumentException(s"Unsupported confirm type: $other")
            }

            complete(sensoryEventStatus)
          }
        }
      } ~
      path("events") {
        get {
          val events = baker.events(requestId).toList
          complete(events)
        }
      } ~
      path(Segment / "bake")  { recipeId =>
        post {
          val processState = baker.bake(recipeId, requestId)
          complete(processState.processId)
        }
      } ~
      path("ingredients") {
        get {

          val ingredients = baker.getIngredients(requestId)

          complete(ingredients)
        }
      } ~
      path("visual_state") {
        get {

          val visualState = baker.getVisualState(requestId)

          complete(visualState)
        }
      }
    }


    val baasRoutes = {

      path("recipe") {
        post {
          entity(as[commonserialize.Recipe]) { recipe =>

            val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

            try {
              println(s"Adding recipe called: ${compiledRecipe.name}")
              val recipeId = baker.addRecipe(compiledRecipe)
              complete(recipeId)
            } catch {
              case e: Exception => {
                println(s"Exception when adding recipe: ${e.getMessage}")
                throw e
              }
            }
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
            complete(s"Interaction: ${interactionImplementation.name} added")
          }
        }
      } ~ pathPrefix(Segment) { recipeRoutes _ }
    }
    baasRoutes
  }
}