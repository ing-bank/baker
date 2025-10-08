package com.ing.baker.runtime.model

import cats.effect.Async
import cats.syntax.all._
import com.ing.baker.runtime.scaladsl.BakerEvent

trait EventStream[F[_]] {

  protected def fetchListeners: F[List[BakerEvent => Unit]]

  def subscribe(listenerFunction: BakerEvent => Unit): F[Unit]

  def publish(event: BakerEvent)(implicit components: BakerComponents[F], async: Async[F]): F[Unit] = {
    for {
      listeners <- fetchListeners
      _ <- listeners.traverse { listener =>
        async
          .delay(listener(event))
          .handleErrorWith { e =>
            async.delay(components.logging.exceptionOnEventListener(e))
          }
      }
    } yield ()
  }
}