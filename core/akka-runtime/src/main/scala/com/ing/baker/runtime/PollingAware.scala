package com.ing.baker.runtime

import com.ing.baker.il.CompiledRecipe
import com.typesafe.scalalogging.LazyLogging
import shapeless.Lazy

import scala.concurrent.{ExecutionContext, Future}

trait PollingAware extends RecipeManager with LazyLogging {

  implicit def ex: ExecutionContext

  abstract override def put(compiledRecipe: CompiledRecipe, createdTime: Long): Future[String] = {
    this.get(compiledRecipe.recipeId).flatMap {
      maybe =>
        if (maybe.isEmpty || (maybe.isDefined && maybe.get._2 < createdTime)) {
          logger.debug(s"Adding/updating recipe ${compiledRecipe.name} : ${compiledRecipe.recipeId}")
          super.put(compiledRecipe, createdTime)
        } else {
          Future.successful(compiledRecipe.recipeId)
        }
    }
  }
}
