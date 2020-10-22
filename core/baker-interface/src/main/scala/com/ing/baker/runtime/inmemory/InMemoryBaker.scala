package com.ing.baker.runtime.inmemory

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.model.Baker

object InMemoryBaker {

  def build(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[Baker[IO]] = {
    for {
      interactionInstanceManager <- InMemoryInteractionInstanceManager.build
      recipeInstanceManager <- InMemoryRecipeInstanceManager.build
      recipeManager <- InMemoryRecipeManager.build
    } yield Baker.build(
      interactionInstanceManager,
      recipeInstanceManager,
      recipeManager,
      ???
    )
  }
}