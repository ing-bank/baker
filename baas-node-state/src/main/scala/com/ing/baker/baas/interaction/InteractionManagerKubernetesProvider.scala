package com.ing.baker.baas.interaction

import akka.actor.ActorSystem
import com.ing.baker.runtime.akka.internal.{InteractionManager, InteractionManagerProvider}
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.FiniteDuration

class InteractionManagerKubernetesProvider extends InteractionManagerProvider {

  def get(config: Config): InteractionManager = {
    val postTimeout = config.as[FiniteDuration]("post-timeout")
    val computationTimeout = config.as[FiniteDuration]("computation-timeout")
    new InteractionManagerKubernetes(ActorSystem("InteractionManagerKubernetes"), postTimeout, computationTimeout)
  }
}