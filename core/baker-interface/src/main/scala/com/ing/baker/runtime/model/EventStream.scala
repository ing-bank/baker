package com.ing.baker.runtime.model

import com.ing.baker.runtime.common.AsyncSupport
import com.ing.baker.runtime.scaladsl.BakerEvent

trait EventStream[F[_]] {

  protected def fetchListeners: F[List[BakerEvent => scala.Unit]]

  def subscribe(listenerFunction: BakerEvent => scala.Unit): F[scala.Unit]

  def publish(event: BakerEvent)(implicit components: BakerComponents[F], async: AsyncSupport[F]): F[scala.Unit] = {
    def notifyListeners(listeners: List[BakerEvent => scala.Unit]): F[scala.Unit] = listeners match {
      case Nil => async.unit
      case listener :: tail =>
        async.flatMap(
          async.handleErrorWith(async.delay(listener(event))) { e =>
            async.delay(components.logging.exceptionOnEventListener(e))
          }
        )(_ => notifyListeners(tail))
    }

    async.flatMap(fetchListeners)(notifyListeners)
  }
}