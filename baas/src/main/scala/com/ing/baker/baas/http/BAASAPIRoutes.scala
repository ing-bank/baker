package com.ing.baker.baas.http

import akka.http.scaladsl.server.{Directives, Route}
import akka.util.ByteString
import com.ing.baker.baas.BAAS
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.baas.interaction.RemoteInteractionImplementation
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.commonserialize
import com.ing.baker.runtime.core.ProcessState

import scala.concurrent.duration._

object BAASAPIRoutes extends Directives {

  implicit val timeout: FiniteDuration = 30 seconds

  def apply(baas: BAAS): Route = {
    val baasRoutes = {
      path("recipe") {
        post {
          entity(as[ByteString]) { string =>
            val byteArray: Array[Byte] = string.toArray
            val deserializedRecipe: commonserialize.Recipe = BAAS.deserializeRecipe(byteArray)
            val compiledRecipe = RecipeCompiler.compileRecipe(deserializedRecipe)
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
          entity(as[ByteString]) { string =>
            val byteArray: Array[Byte] = string.toArray
            val request = kryoPool.fromBytes(byteArray).asInstanceOf[AddInteractionHTTPRequest]
            println(s"Request received for adding interaction: $request}")

            //Create a RemoteInteractionImplementation
            val interactionImplementation = RemoteInteractionImplementation(request.name, request.hostname, request.port)
            println(s"Adding interaction called: ${request.name}")


            //Register it to BAAS
            baas.baker.addInteractionImplementation(interactionImplementation)
            complete("send")
          }
        }
      } ~
      path("event") {
        post {
          entity(as[ByteString]) { string =>
            val byteArray: Array[Byte] = string.toArray
            val request = kryoPool.fromBytes(byteArray).asInstanceOf[HandleEventHTTPRequest]
            println(s"Request received for handling event: $request}")

            val recipeHandler = baas.baker.getRecipeHandler(request.recipeName)

            val sensoryEventStatus = recipeHandler.handleEvent(request.requestId, request.runtimeEvent)

            val response = HandleEventHTTPResponse(sensoryEventStatus)
            complete(kryoPool.toBytesWithClass(response))
          }
        }
      } ~
      path("bake") {
        post {
          entity(as[ByteString]) { string =>
            val byteArray: Array[Byte] = string.toArray
            val request = kryoPool.fromBytes(byteArray).asInstanceOf[BakeHTTPRequest]
            println(s"Request received for baking: $request}")

            val recipeHandler = baas.baker.getRecipeHandler(request.recipeName)

            val requestId: ProcessState = recipeHandler.bake(request.requestId)

            val response = BakeHTTPResponse()
            complete(kryoPool.toBytesWithClass(response))
          }
        }
      } ~
      path("state") {
        post {
          entity(as[ByteString]) { string =>
            val byteArray: Array[Byte] = string.toArray
            val request = kryoPool.fromBytes(byteArray).asInstanceOf[GetStateHTTPRequest]
            println(s"Request received for getting state: $request}")

            val recipeHandler = baas.baker.getRecipeHandler(request.recipeName)

            val processState: ProcessState =
              recipeHandler.getProcessState(request.requestId)

            val visualState = recipeHandler.getVisualState(request.requestId)

            val response = GetStateHTTResponse(processState, visualState)
            complete(kryoPool.toBytesWithClass(response))
          }
        }
      }
    }
    baasRoutes
  }
}