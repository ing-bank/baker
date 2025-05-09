package com.ing.baker.runtime.recipe_manager

import com.ing.baker.runtime.common.RecipeRecord
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.{ExecutionContext, Future}

/**
 * This trait is used to avoid replacing recipes with elder or same creation time.
 */
trait PollingAware extends RecipeManager with LazyLogging {

  implicit def ex: ExecutionContext

  abstract override def put(recipeRecord: RecipeRecord): Future[String] = {
    this.get(recipeRecord.recipeId).flatMap {
      maybeInCache =>
        if (maybeInCache.isEmpty || (maybeInCache.isDefined && maybeInCache.get.updated < recipeRecord.updated)) {
          logger.info(s"${if (maybeInCache.isEmpty) "Adding" else "Updating"} recipe ${recipeRecord.name} : ${recipeRecord.recipeId}")
          super.put(recipeRecord)
        } else {
          Future.successful(recipeRecord.recipeId)
        }
    }
  }
}
