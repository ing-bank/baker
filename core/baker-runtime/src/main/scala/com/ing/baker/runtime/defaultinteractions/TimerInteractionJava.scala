package com.ing.baker.runtime.defaultinteractions

import java.time.Duration
import java.util.concurrent.TimeUnit

import cats.effect.Async
import cats.syntax.all._

import scala.concurrent.duration.FiniteDuration

class TimerInteractionJava[F[_]](skipWait: Boolean)(implicit F: Async[F]) {

  class TimeWaited()

  val name = "TimerInteraction"

  def apply(WaitTime: Duration): F[TimeWaited] = {
    if(skipWait)
      F.pure(new TimeWaited)
    else
      F.sleep(FiniteDuration.apply(WaitTime.toMillis, TimeUnit.MILLISECONDS)).as(new TimeWaited)
  }
}
