package com.ing.baker.runtime.core

import akka.actor.ActorSystem
import com.typesafe.config.{Config, ConfigFactory}
import net.ceedubs.ficus.Ficus._

object ActorSystemProvider {

  def get(config: Config): ActorSystem = {
    config.getAs[String]("baker.engine.actor-system-provider")
      .map { actorSystemProviderPath =>
        try {
          val clazz = Class.forName(actorSystemProviderPath).newInstance()
          clazz match {
            case provider: ActorSystemProvider => provider.apply(config)
            case _ => throw new IllegalArgumentException("baker.engine.actor-system-provider does not point to a actor system provider")
          }
        } catch {
          case _: InstantiationException => throw new IllegalArgumentException("baker.engine.actor-system-provider points to a class without default constructor")
          case e: Throwable => throw e
        }
      }.getOrElse(new DefaultActorSystemProvider()(config))
  }

  def apply(config: Config): ActorSystem = ActorSystemProvider.get(config)

  def get(): ActorSystem = ActorSystemProvider.get(ConfigFactory.load())

  def apply(): ActorSystem = ActorSystemProvider.get()
}

trait ActorSystemProvider {
  def apply(config: Config): ActorSystem
}