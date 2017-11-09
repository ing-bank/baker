package com.ing.baker.baas.http

import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.BAAS
import com.ing.baker.baas.interaction.RemoteInteractionImplementation
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.commonserialize
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}

import scala.concurrent.duration._

object BAASAPIRoutes extends Directives with BaasMarshalling {

  implicit val timeout: FiniteDuration = 30 seconds

  def apply(baas: BAAS): Route = {

    def recipeRoutes(recipeName: String, requestId: String) = {

      val recipeHandler = baas.baker.getRecipeHandler(recipeName)

      path("event") {
        post {
          entity(as[RuntimeEvent]) { event =>

            val sensoryEventStatus = recipeHandler.handleEvent(requestId, event)
            val response = HandleEventHTTPResponse(sensoryEventStatus)

            complete(response)
          }
        }
      } ~
        path("bake") {
          post {
            recipeHandler.bake(requestId)

            val response = BakeHTTPResponse()
            complete(response)
          }
        } ~
        path("state") {
          get {

            val processState: ProcessState = recipeHandler.getProcessState(requestId)
            val visualState = recipeHandler.getVisualState(requestId)
            val response = GetStateHTTResponse(processState, visualState)

            complete(response)
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
              baas.baker.addRecipe(compiledRecipe)
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
            baas.baker.addInteractionImplementation(interactionImplementation)

            //return response
            complete(s"Interaction: ${interactionImplementation.name} added")
          }
        }
      } ~ pathPrefix(Segment / Segment) { recipeRoutes _ }
    }
    baasRoutes
  }
}