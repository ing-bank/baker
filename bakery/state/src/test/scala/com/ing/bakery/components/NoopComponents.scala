package com.ing.bakery.components

import cats.effect.IO
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.baker.runtime.recipe_manager.RecipeManager

import scala.concurrent.Future
object NoopComponents {
  object TestInteractionManager extends InteractionManager[IO] {
    override def listAll: IO[List[InteractionInstance[IO]]] = IO.pure(List.empty)
  }
}
