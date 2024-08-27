package com.ing.bakery

import akka.actor.ActorSystem
import cats.effect.IO
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.RecipeManager
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.bakery.Bakery.akkaBakery
import com.typesafe.config.Config

import java.io.Closeable

class ClosableBakery(baker: Baker,
                     system: ActorSystem,
                     close: IO[Unit]
                    ) extends AkkaBakery(baker, system) with Closeable {
  override def close(): Unit = close.unsafeRunSync()
}

object ClosableBakery {
  /**
    * Create bakery instance as external context
    *
    * @param externalContext optional external context in which Bakery is running, e.g. Spring context
    */
  def instance(optionalConfig: Option[Config],
               externalContext: Option[Any],
               interactionManager: Option[InteractionManager[IO]] = None,
               recipeManager: Option[RecipeManager] = None): ClosableBakery = {
    val (baker: AkkaBakery, close: IO[Unit]) = akkaBakery(optionalConfig, externalContext, interactionManager, recipeManager).allocated.unsafeRunSync()
    new ClosableBakery(baker.baker, baker.system, close)
  }
}
