package com.ing.baker.baas.http

import akka.http.scaladsl.server.{Directives, Rejection, Route}
import akka.util.ByteString
import com.ing.baker.baas.BAAS
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
      }
    }
    baasRoutes
  }
}