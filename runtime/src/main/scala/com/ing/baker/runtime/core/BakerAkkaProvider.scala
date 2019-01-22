package com.ing.baker.runtime.core

import akka.actor.ActorSystem
import com.typesafe.config.Config

class BakerAkkaProvider extends BakerProvider {
  override def apply(config: Config): Baker = {
    implicit val actorSystem: ActorSystem = ActorSystemProvider.get(config)
    new AkkaBaker(config)
  }
}