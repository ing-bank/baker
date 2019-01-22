package com.ing.baker.runtime.core

import akka.actor.ActorSystem
import com.typesafe.config.Config


class BakerAkkaProvider extends BakerProvider {
  def apply(config: Config): Baker = {
    val actorSystemName: String =
      if(config.hasPath("baker.engine.akka-baker.actor-system-name"))
       config.getString("baker.engine.akka-baker.actor-system-name")
      else
        "BakerAkkaActorSystem"
    implicit val actorSystem: ActorSystem = ActorSystem(actorSystemName, config)
    new AkkaBaker()
  }
}