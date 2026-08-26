package com.ing.baker.runtime.defaultinteractions

import com.ing.baker.runtime.catseffect.AsyncSupport
import java.time.Duration
import java.util.concurrent.TimeUnit

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
