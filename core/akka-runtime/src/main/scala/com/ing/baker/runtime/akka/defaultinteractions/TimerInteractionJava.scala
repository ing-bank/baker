package com.ing.baker.runtime.akka.defaultinteractions

import java.time.Duration
import java.util.concurrent.TimeUnit

import cats.effect.{IO, Timer}

import scala.concurrent.duration.FiniteDuration

class TimerInteractionJava(skipWait: Boolean)(implicit timer: Timer[IO]) {

  class TimeWaited()

  val name = "TimerInteraction"

  def apply(WaitTime: Duration): IO[TimeWaited] = {
    if(skipWait)
      IO.pure(new TimeWaited)
    else
      IO.sleep(FiniteDuration.apply(WaitTime.toMillis, TimeUnit.MILLISECONDS)) *> IO(new TimeWaited)
  }
}
