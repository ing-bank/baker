package com.ing.baker.runtime.inmemory

import cats.effect.{ConcurrentEffect, ContextShift, IO, Timer}
import cats.~>
import com.ing.baker.runtime.inmemory.InMemoryBaker.build
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.model.{Baker, BakerComponents, BakerConfig}

import scala.concurrent._

object InMemoryBaker {

  def build(config: BakerConfig = BakerConfig())(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[Baker[IO]] = for {
    interactionInstanceManager <- InMemoryInteractionInstanceManager.build
    recipeInstanceManager <- InMemoryRecipeInstanceManager.build
    recipeManager <- InMemoryRecipeManager.build
    eventStream <- InMemoryEventStream.build
  } yield {
    implicit val components: BakerComponents[IO] =
      BakerComponents[IO](interactionInstanceManager, recipeInstanceManager, recipeManager, eventStream)
    new InMemoryBaker(config)
  }
}

object InMemoryBakerJava {

  def java(config: BakerConfig): javadsl.Baker = {
    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)
    val bakerF = build(config).unsafeRunSync().asDeprecatedFutureImplementation(
      new (IO ~> Future) {
        def apply[A](fa: IO[A]): Future[A] = fa.unsafeToFuture()
      },
      new (Future ~> IO) {
        def apply[A](fa: Future[A]): IO[A] = IO.fromFuture(IO(fa))
      }
    )
    new javadsl.Baker(bakerF)
  }

  def java() : javadsl.Baker = {
    java(BakerConfig())
  }
}

final class InMemoryBaker(val config: BakerConfig)(implicit components: BakerComponents[IO], effect: ConcurrentEffect[IO], timer: Timer[IO]) extends Baker[IO] {

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): IO[Unit] = IO.unit
}