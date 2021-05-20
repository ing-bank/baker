package com.ing.baker.runtime.inmemory

import cats.effect.{ConcurrentEffect, ContextShift, IO, Timer}
import cats.~>
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.model.{BakerComponents, BakerF}
import com.ing.baker.runtime.scaladsl.InteractionInstanceF

import java.util
import scala.concurrent._
import java.util.{List => JavaList}
import scala.collection.JavaConverters._

object InMemoryBaker {

  def build(config: BakerF.Config = BakerF.Config(),
            implementations: List[InteractionInstanceF[IO]])(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[BakerF[IO]] = for {
    recipeInstanceManager <- InMemoryRecipeInstanceManager.build
    recipeManager <- InMemoryRecipeManager.build
    eventStream <- InMemoryEventStream.build
    interactions <- InMemoryInteractions.build(implementations)
  } yield buildWith(BakerComponents[IO](interactions, recipeInstanceManager, recipeManager, eventStream), config)

  def buildWith(components: BakerComponents[IO],
                config: BakerF.Config = BakerF.Config())(implicit timer: Timer[IO], cs: ContextShift[IO]): BakerF[IO] = {
    implicit val c: BakerComponents[IO] = components
    new InMemoryBakerImpl(config)
  }

  def java(implementations: JavaList[AnyRef]) = {
    java(BakerF.Config(), implementations)
  }

  def java(config: BakerF.Config, implementations: JavaList[AnyRef]): javadsl.Baker = {
    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)
    val bakerF = build(config, implementations.asScala.map(InteractionInstanceF.unsafeFrom[IO]).toList)
      .unsafeRunSync().asDeprecatedFutureImplementation(
      new (IO ~> Future) {
        def apply[A](fa: IO[A]): Future[A] = fa.unsafeToFuture()
      },
      new (Future ~> IO) {
        def apply[A](fa: Future[A]): IO[A] = IO.fromFuture(IO(fa))
      }
    )
    new javadsl.Baker(bakerF)
  }

  def java(): javadsl.Baker = {
    java(BakerF.Config(), new util.ArrayList[AnyRef]())
  }
}

final class InMemoryBakerImpl(val config: BakerF.Config)(implicit components: BakerComponents[IO], effect: ConcurrentEffect[IO], timer: Timer[IO]) extends BakerF[IO] {

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): IO[Unit] = IO.unit
}