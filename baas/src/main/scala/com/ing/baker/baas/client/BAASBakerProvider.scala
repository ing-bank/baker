package com.ing.baker.baas.client

import akka.actor.ActorSystem
import com.ing.baker.runtime.core.{Baker, BakerProvider}
import com.typesafe.config.Config

class BAASBakerProvider extends BakerProvider{
  override def apply(config: Config): Baker = {
    val actorSystemName: String =
      if(config.hasPath("baker.engine.baas.actor-system-name"))
        config.getString("baker.engine.baas.actor-system-name")
      else
        "BakerAkkaActorSystem"
    implicit val actorSystem: ActorSystem = ActorSystem(actorSystemName, config)

    new BAASClient(
      config.getString("baker.engine.baas.client-host"),
      config.getInt("baker.engine.baas.client-port"),
      config.getString("baker.engine.baas.baas-host"),
      config.getInt("baker.engine.baas.baas-port"))
  }
}
