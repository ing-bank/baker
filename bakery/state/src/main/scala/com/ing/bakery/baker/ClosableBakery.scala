package com.ing.bakery.baker

import java.io.Closeable

import akka.actor.ActorSystem
import cats.effect.IO
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.RecipeManager
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.bakery.baker.Bakery.resource

import scala.concurrent.ExecutionContext

class ClosableBakery(baker: Baker,
                     executionContext: ExecutionContext,
                     system: ActorSystem,
                     close: IO[Unit]) extends Bakery(baker, executionContext, system) with Closeable {
  override def close(): Unit = close.unsafeRunSync()
}

object ClosableBakery {
  /**
    * Create bakery instance as external context
    * @param externalContext optional external context in which Bakery is running, e.g. Spring context
    * @return
    */
  def instance(externalContext: Option[Any],
               interactionManager: Option[InteractionManager[IO]] = None,
               recipeManager: Option[RecipeManager] = None): ClosableBakery = {
    val (baker: Bakery, close: IO[Unit]) = resource(externalContext, interactionManager, recipeManager).allocated.unsafeRunSync()
    new ClosableBakery(baker.baker, baker.executionContext, baker.system, close)
  }
}