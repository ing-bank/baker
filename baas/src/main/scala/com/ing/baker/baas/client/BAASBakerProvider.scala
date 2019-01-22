package com.ing.baker.baas.client

import akka.actor.ActorSystem
import com.ing.baker.runtime.core.{ActorSystemProvider, Baker, BakerProvider}
import com.typesafe.config.Config

class BAASBakerProvider extends BakerProvider{
  override def apply(config: Config): Baker = {
    implicit val actorSystem: ActorSystem = ActorSystemProvider.get(config)

    new BAASClient(
      config,
      config.getString("baker.engine.baas.client-host"),
      config.getInt("baker.engine.baas.client-port"),
      config.getString("baker.engine.baas.baas-host"),
      config.getInt("baker.engine.baas.baas-port"))
  }
}
