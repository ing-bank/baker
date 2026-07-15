package com.ing.baker.runtime.defaultinteractions

import cats.effect.Async
import cats.syntax.all._

import scala.concurrent.duration.FiniteDuration

class TimerInteraction[F[_]](skipWait: Boolean)(implicit F: Async[F]) {

  class TimeWaited()

  def apply(WaitTime: FiniteDuration): F[TimeWaited] = {
    if(skipWait)
      F.pure(new TimeWaited)
    else
      F.sleep(WaitTime).as(new TimeWaited)
  }
}
