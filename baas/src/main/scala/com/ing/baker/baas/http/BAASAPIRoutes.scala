package com.ing.baker.baas.http

import akka.http.scaladsl.server.{Directives, Route}
import akka.util.ByteString
import com.ing.baker.baas.BAAS
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.baas.interaction.RemoteInteractionImplementation
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.commonserialize

object BAASAPIRoutes extends Directives {

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
      }
    }
    baasRoutes
  }
}