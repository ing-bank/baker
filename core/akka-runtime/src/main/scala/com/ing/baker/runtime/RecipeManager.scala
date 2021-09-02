package com.ing.baker.runtime

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord

import scala.concurrent.Future

trait RecipeManager {
  def put(recipeRecord: RecipeRecord): Future[String]

  def get(recipeId: String): Future[Option[RecipeRecord]]

  def all: Future[Seq[RecipeRecord]]
}
