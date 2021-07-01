package com.ing.baker.runtime.inmemory.defaultinteractions

import cats.effect.{IO, Timer}

import scala.concurrent.duration.FiniteDuration

class TimerInteraction(skipWait: Boolean)(implicit timer: Timer[IO]) {

  class TimeWaited()

  def apply(WaitTime: FiniteDuration): IO[TimeWaited] = {
    if(skipWait)
      IO.pure(new TimeWaited)
    else
      IO.sleep(WaitTime) *> IO(new TimeWaited)
  }
}
