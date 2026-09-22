package com.ing.baker.runtime.defaultinteractions

import com.ing.baker.runtime.catseffect.AsyncSupport
import scala.concurrent.duration.FiniteDuration

class TimerInteraction[F[_]](skipWait: Boolean)(implicit F: AsyncSupport[F]) {

  class TimeWaited

  def apply(WaitTime: FiniteDuration): F[TimeWaited] = {
    if(skipWait)
      F.pure(new TimeWaited)
    else
      F.map(F.sleep(WaitTime))(_ => new TimeWaited)
  }
}
