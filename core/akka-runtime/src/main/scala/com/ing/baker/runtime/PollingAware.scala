package com.ing.baker.runtime

import com.ing.baker.il.CompiledRecipe

import scala.concurrent.{ExecutionContext, Future}

trait PollingAware extends RecipeManager {

  implicit def ex: ExecutionContext

  abstract override def put(compiledRecipe: CompiledRecipe, createdTime: Long): Future[String] = {
    this.get(compiledRecipe.recipeId).flatMap {
      maybe =>
        if (maybe.isEmpty || (maybe.isDefined && maybe.get._2 < createdTime)) {
          super.put(compiledRecipe, createdTime)
        } else {
          Future.successful(compiledRecipe.recipeId)
        }
    }
  }
}
