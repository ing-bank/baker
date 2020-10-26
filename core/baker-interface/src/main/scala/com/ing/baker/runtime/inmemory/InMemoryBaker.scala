package com.ing.baker.runtime.inmemory

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.model.{Baker, BakerComponents}

object InMemoryBaker {

  def build(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[Baker[IO]] = for {
    interactionInstanceManager <- InMemoryInteractionInstanceManager.build
    recipeInstanceManager <- InMemoryRecipeInstanceManager.build
    recipeManager <- InMemoryRecipeManager.build
  } yield {
    implicit val components: BakerComponents[IO] =
      BakerComponents[IO](interactionInstanceManager, recipeInstanceManager, recipeManager, ???)
    new InMemoryBaker()
  }
}

final class InMemoryBaker(implicit components: BakerComponents[IO], timer: Timer[IO]) extends Baker[IO] {

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): IO[Unit] = IO.unit
}