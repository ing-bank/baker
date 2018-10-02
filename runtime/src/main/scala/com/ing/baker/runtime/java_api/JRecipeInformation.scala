package com.ing.baker.runtime.java_api

import akka.japi.Option.Some
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.protobuf.Node.OneofNode.Empty
import com.ing.baker.runtime.core.RecipeInformation

import scala.collection.JavaConverters._

object  JRecipeInformation {
  def fromRecipeInformation(recipeInformation: RecipeInformation): JRecipeInformation = {
    JRecipeInformation(recipeInformation.recipeId,
      recipeInformation.compiledRecipe,
      recipeInformation.recipeCreatedTime,
      Option(recipeInformation.errors).getOrElse(Set.empty[String]).asJava)
  }
}

case class JRecipeInformation(recipeId: String, compiledRecipe: CompiledRecipe, recipeCreatedTime: Long, errors: java.util.Set[String]) {
}