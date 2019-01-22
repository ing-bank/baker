package com.ing.baker.runtime.core

import akka.actor.ActorSystem
import com.typesafe.config.Config

class DefaultActorSystemProvider extends ActorSystemProvider {
  override def apply(config: Config): ActorSystem = {
    val actorSystemName: String =
      if(config.hasPath("baker.engine.actor-system-name"))
        config.getString("baker.engine.actor-system-name")
      else
        "BakerActorSystem"

    ActorSystem(actorSystemName, config)
  }
}
