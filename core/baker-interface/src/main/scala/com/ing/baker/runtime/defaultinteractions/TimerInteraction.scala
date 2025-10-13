package com.ing.baker.runtime.defaultinteractions

import cats.effect.IO

import scala.concurrent.duration.FiniteDuration

class TimerInteraction(skipWait: Boolean) {

  class TimeWaited()

  def apply(WaitTime: FiniteDuration): IO[TimeWaited] = {
    if(skipWait)
      IO.pure(new TimeWaited)
    else
      IO.sleep(WaitTime) *> IO(new TimeWaited)
  }
}
