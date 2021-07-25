package com.ing.baker.runtime.defaultinteractions

import cats.effect.IO

import scala.concurrent.duration.FiniteDuration
import cats.effect.Temporal

class TimerInteraction(skipWait: Boolean)(implicit timer: Temporal[IO]) {

  class TimeWaited()

  def apply(WaitTime: FiniteDuration): IO[TimeWaited] = {
    if(skipWait)
      IO.pure(new TimeWaited)
    else
      IO.sleep(WaitTime) *> IO(new TimeWaited)
  }
}
