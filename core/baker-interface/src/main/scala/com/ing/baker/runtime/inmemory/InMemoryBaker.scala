package com.ing.baker.runtime.inmemory

import cats.effect.{ConcurrentEffect, ContextShift, IO, Timer}
import com.ing.baker.runtime.model.{Baker, BakerComponents, TimeoutsConfig}

object InMemoryBaker {

  def build(timeouts: TimeoutsConfig = TimeoutsConfig())(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[Baker[IO]] = for {
    interactionInstanceManager <- InMemoryInteractionInstanceManager.build
    recipeInstanceManager <- InMemoryRecipeInstanceManager.build
    recipeManager <- InMemoryRecipeManager.build
    eventStream <- InMemoryEventStream.build
  } yield {
    implicit val components: BakerComponents[IO] =
      BakerComponents[IO](interactionInstanceManager, recipeInstanceManager, recipeManager, eventStream)
    new InMemoryBaker(timeouts)
  }
}

final class InMemoryBaker(val timeouts: TimeoutsConfig)(implicit components: BakerComponents[IO], effect: ConcurrentEffect[IO], timer: Timer[IO]) extends Baker[IO] {

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): IO[Unit] = IO.unit
}