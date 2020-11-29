package com.ing.baker.runtime.model

import cats.effect.{Effect, IO}
import cats.implicits._
import com.ing.baker.runtime.scaladsl.BakerEvent

trait EventStream[F[_]] {

  protected def fetchListeners: F[List[BakerEvent => Unit]]

  def subscribe(listenerFunction: BakerEvent => Unit): F[Unit]

  def publish(event: BakerEvent)(implicit components: BakerComponents[F], effect: Effect[F]): F[Unit] = {
    for {
      listeners <- fetchListeners
      _ <- listeners.traverse { listener =>
        effect.runAsync(effect.delay(listener(event))) {
          case Right(_) => IO.unit
          case Left(e) => effect.toIO(components.logging.exceptionOnEventListener(e))
        }
      }.to[F]
    } yield ()
  }
}
