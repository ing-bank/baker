package com.ing.baker.runtime.defaultinteractions

import java.time.Duration
import java.util.concurrent.TimeUnit

import com.ing.baker.runtime.common.AsyncSupport

import scala.concurrent.duration.FiniteDuration

class TimerInteractionJava[F[_]](skipWait: Boolean)(implicit F: AsyncSupport[F]) {

  class TimeWaited

  val name = "TimerInteraction"

  def apply(WaitTime: Duration): F[TimeWaited] = {
    if(skipWait)
      F.pure(new TimeWaited)
    else
      F.map(F.sleep(FiniteDuration.apply(WaitTime.toMillis, TimeUnit.MILLISECONDS)))(_ => new TimeWaited)
  }
}
