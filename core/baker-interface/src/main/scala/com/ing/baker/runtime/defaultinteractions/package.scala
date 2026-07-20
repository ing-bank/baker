package com.ing.baker.runtime

import cats.effect.IO
import com.ing.baker.runtime.model.InteractionInstance
import com.typesafe.config.ConfigFactory

package object defaultinteractions {
  def all: List[InteractionInstance[IO]] = {
    val path = "baker.default-interactions.timer.skip"
    val config = ConfigFactory.load()
    val skipWait = config.hasPath(path) && config.getBoolean(path)
    List(
      InteractionInstance.unsafeFrom[IO](new TimerInteraction[IO](skipWait)),
      InteractionInstance.unsafeFrom[IO](new TimerInteractionJava[IO](skipWait)))
  }
}
