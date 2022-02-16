package com.ing.baker.runtime.akka.actor.process_index

import com.github.blemale.scaffeine.{AsyncLoadingCache, Scaffeine}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.recipe_manager.RecipeManager

import scala.concurrent.Await.result
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

/**
  * Singleton concurrent cache used by all sharding instances of ProcessIndexActor, reducing the memory allocation needed.
  *
  * @param recipeManager RecipeManager
  * @param updateCacheTimeout baker.process-index-update-cache-timeout
  * @param cacheSize baker.recipe-cache-size
  * @param ex
  */
class RecipeCache(recipeManager: RecipeManager,
                  updateCacheTimeout: FiniteDuration,
                  cacheSize: Int)
                 (implicit val ex: ExecutionContext) {

  private val cache: AsyncLoadingCache[String, Option[(CompiledRecipe, Long)]] =
    Scaffeine()
      .recordStats()
      .expireAfterWrite(4.hours)
      .maximumSize(cacheSize)
      .buildAsyncFuture((recipeId: String) =>
        recipeManager.get(recipeId).map(_.map(r => (r.recipe, r.updated))))

  def getBlocking(recipeId: String): Option[(CompiledRecipe, Long)] = result(cache.get(recipeId), updateCacheTimeout)
}