package com.ing.baker.runtime.inmemory

import cats.effect.{ConcurrentEffect, ContextShift, IO, Timer}
import cats.~>
import com.ing.baker.runtime.javadsl.BakerConfig
import com.ing.baker.runtime.model.{BakerComponents, BakerF, InteractionInstance}
import com.ing.baker.runtime.{defaultinteractions, javadsl}

import java.util
import java.util.{List => JavaList}
import scala.annotation.nowarn
import scala.collection.JavaConverters._
import scala.concurrent._

object InMemoryBaker {

  def build(config: BakerF.Config = BakerF.Config(),
            implementations: List[InteractionInstance[IO]])(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[BakerF[IO]] = for {
    recipeInstanceManager <- InMemoryRecipeInstanceManager.build(config.idleTimeout, config.retentionPeriodCheckInterval)
    recipeManager <- InMemoryRecipeManager.build
    eventStream <- InMemoryEventStream.build
    interactions <- InMemoryInteractionManager.build(implementations ++ defaultinteractions.all)
  } yield buildWith(BakerComponents[IO](interactions, recipeInstanceManager, recipeManager, eventStream), config)

  def buildWith(components: BakerComponents[IO],
                config: BakerF.Config = BakerF.Config())(implicit timer: Timer[IO], cs: ContextShift[IO]): BakerF[IO] = {
    implicit val c: BakerComponents[IO] = components
    new InMemoryBakerImpl(config)
  }

  @nowarn
  def java(config: BakerF.Config, implementations: JavaList[AnyRef]): javadsl.Baker = {
    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)
    val interactions = implementations.asScala.map{
      case it: InteractionInstance[IO] => it
      case it: com.ing.baker.runtime.javadsl.InteractionInstance =>
        it.asScala.translate[IO](new (Future ~> IO) {
          def apply[A](fa: Future[A]): IO[A] = IO.fromFuture(IO(fa))
        })
      case it => InteractionInstance.unsafeFrom[IO](it)
    }
    val bakerF = build(config, interactions.toList)
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

  def java(config: BakerConfig, implementations: JavaList[AnyRef]): javadsl.Baker = {
    java(config.toBakerFConfig(), implementations)
  }

  def java(implementations: JavaList[AnyRef]): javadsl.Baker = {
    java(BakerF.Config(), implementations)
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
