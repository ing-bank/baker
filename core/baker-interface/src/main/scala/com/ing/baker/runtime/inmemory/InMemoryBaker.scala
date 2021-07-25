package com.ing.baker.runtime.inmemory

import java.util
import java.util.{List => JavaList}

import cats.effect.{ConcurrentEffect, IO}
import cats.~>
import com.ing.baker.runtime.{defaultinteractions, javadsl}
import com.ing.baker.runtime.model.{BakerComponents, BakerF, InteractionInstance}

import scala.collection.JavaConverters._
import scala.concurrent._
import cats.effect.Temporal

object InMemoryBaker {

  def build(config: BakerF.Config = BakerF.Config(),
            implementations: List[InteractionInstance[IO]])(implicit timer: Temporal[IO]): IO[BakerF[IO]] = for {
    recipeInstanceManager <- InMemoryRecipeInstanceManager.build
    recipeManager <- InMemoryRecipeManager.build
    eventStream <- InMemoryEventStream.build
    interactions <- InMemoryInteractionManager.build(implementations ++ defaultinteractions.getDefaultInteractions)
  } yield buildWith(BakerComponents[IO](interactions, recipeInstanceManager, recipeManager, eventStream), config)

  def buildWith(components: BakerComponents[IO],
                config: BakerF.Config = BakerF.Config())(implicit timer: Temporal[IO]): BakerF[IO] = {
    implicit val c: BakerComponents[IO] = components
    new InMemoryBakerImpl(config)
  }

  def java(config: BakerF.Config, implementations: JavaList[AnyRef]): javadsl.Baker = {
    implicit val timer: Temporal[IO] = IO.timer(ExecutionContext.global)
    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)
    val bakerF = build(config, implementations.asScala.map(InteractionInstance.unsafeFrom[IO]).toList)
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

  def java(implementations: JavaList[AnyRef]): javadsl.Baker = {
    java(BakerF.Config(), implementations)
  }

  def java(): javadsl.Baker = {
    java(BakerF.Config(), new util.ArrayList[AnyRef]())
  }
}

final class InMemoryBakerImpl(val config: BakerF.Config)(implicit components: BakerComponents[IO], effect: ConcurrentEffect[IO], timer: Temporal[IO]) extends BakerF[IO] {

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): IO[Unit] = IO.unit
}