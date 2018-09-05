package com.ing.baker.runtime.java_api

import com.ing.baker.runtime.core.RecipeHealth

import scala.collection.JavaConverters._

object JRecipeHealth {
  def fromRecipeHealth(recipeHealth: RecipeHealth): JRecipeHealth = {
    JRecipeHealth(recipeHealth.recipeId, recipeHealth.recipeName, recipeHealth.errors.asJava)
  }
}

case class JRecipeHealth(recipeId: String, recipeName: String, errors: java.util.Set[String])