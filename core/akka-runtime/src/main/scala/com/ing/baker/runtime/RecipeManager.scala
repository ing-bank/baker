package com.ing.baker.runtime

import com.ing.baker.il.CompiledRecipe

import scala.concurrent.Future

trait RecipeManager {
  def put(compiledRecipe: CompiledRecipe, createdTime: Long): Future[String]

  def get(recipeId: String): Future[Option[(CompiledRecipe, Long)]]

  def all: Future[Seq[(CompiledRecipe, Long)]]
}
