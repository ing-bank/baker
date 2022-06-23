package com.ing.baker.runtime

import cats.effect.IO
import com.ing.baker.runtime.model.InteractionInstanceF
import com.typesafe.config.ConfigFactory

package object defaultinteractions {
  def all: List[InteractionInstanceF[IO]] = {
    val path = "baker.default-interactions.timer.skip"
    val config = ConfigFactory.load()
    val skipWait = config.hasPath(path) && config.getBoolean(path)
    List(
      InteractionInstanceF.unsafeFrom(new TimerInteraction(skipWait)(IO.timer(scala.concurrent.ExecutionContext.global))),
      InteractionInstanceF.unsafeFrom(new TimerInteractionJava(skipWait)(IO.timer(scala.concurrent.ExecutionContext.global))))
  }
}
