package com.ing.baker.runtime.inmemory

import cats.effect.IO
import com.ing.baker.runtime.model.InteractionInstance
import com.typesafe.config.{Config, ConfigFactory}

package object defaultinteractions {
  def getDefaultInteractions(): List[InteractionInstance[IO]] = {
    val path = "baker.default-interactions.timer.skip"
    val config = ConfigFactory.load()
    val skipWait = config.hasPath(path) && config.getBoolean(path)
    List(
      InteractionInstance.unsafeFrom(new TimerInteraction(skipWait)(IO.timer(scala.concurrent.ExecutionContext.global))),
      InteractionInstance.unsafeFrom(new TimerInteractionJava(skipWait)(IO.timer(scala.concurrent.ExecutionContext.global))))
  }
}