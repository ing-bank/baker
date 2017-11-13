package com.ing.baker.baas.http

import akka.actor.ActorSystem
import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.interaction.RemoteInteractionImplementation
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.commonserialize
import com.ing.baker.runtime.core.{Baker, RuntimeEvent}

import scala.concurrent.duration._

object APIRoutes extends Directives with BaasMarshalling {

  implicit val timeout: FiniteDuration = 30 seconds

  val defaultEventConfirm = "receive"

  def apply(baker: Baker)(implicit actorSystem: ActorSystem): Route = {

    def recipeRoutes(recipeName: String, requestId: String) = {

      val recipeHandler = baker.getRecipeHandler(recipeName)

      path("event") {
        post {
          (entity(as[RuntimeEvent]) & parameter('confirm.as[String] ?)) { (event, confirm) =>

            val sensoryEventStatus = confirm.getOrElse(defaultEventConfirm) match {
              case "received"  => recipeHandler.handleEventAsync(requestId, event).confirmReceived()
              case "completed" => recipeHandler.handleEventAsync(requestId, event).confirmCompleted()
              case other      => throw new IllegalArgumentException(s"Unsupported confirm type: $other")
            }

            complete(sensoryEventStatus)
          }
        }
      } ~
      path("bake") {
        post {
          val processState = recipeHandler.bake(requestId)

          complete(processState)
        }
      } ~
      path("state") {
        get {

          val processState = recipeHandler.getProcessState(requestId)

          complete(processState)
        }
      } ~
      path("visual_state") {
        get {

          val visualState = recipeHandler.getVisualState(requestId)

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
              baker.addRecipe(compiledRecipe)
            } catch {
              case e: Exception => {
                println(s"Exception when adding recipe: ${e.getMessage}")
                throw e
              }
            }
            complete(compiledRecipe.getRecipeVisualization)
          }
        }
      } ~
      path("implementation") {
        post {
          entity(as[AddInteractionHTTPRequest]) { request =>

            //Create a RemoteInteractionImplementation
            val interactionImplementation = RemoteInteractionImplementation(request.name, request.hostname, request.port)
            println(s"Adding interaction called: ${request.name}")

            //Register it to BAAS
            baker.addInteractionImplementation(interactionImplementation)

            //return response
            complete(s"Interaction: ${interactionImplementation.name} added")
          }
        }
      } ~ pathPrefix(Segment / Segment) { recipeRoutes _ }
    }
    baasRoutes
  }
}