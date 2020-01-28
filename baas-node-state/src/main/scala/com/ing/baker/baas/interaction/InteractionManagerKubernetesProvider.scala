package com.ing.baker.baas.interaction

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.runtime.akka.internal.{InteractionManager, InteractionManagerProvider}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.{Config, ConfigFactory}
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.FiniteDuration

class InteractionManagerKubernetesProvider extends InteractionManagerProvider {

  def get(config: Config): InteractionManager = {
    val postTimeout = config.as[FiniteDuration]("post-timeout")
    val computationTimeout = config.as[FiniteDuration]("computation-timeout")

    val akkaConfig = ConfigFactory.empty()

    val actorSystem: ActorSystem = ActorSystem("InteractionManagerKubernetesSystem", akkaConfig)
    val mat: Materializer = ActorMaterializer()(actorSystem)
    val encryption: Encryption = {
      val encryptionEnabled = config.getAs[Boolean]("encryption.enabled").getOrElse(false)
      if (encryptionEnabled) new Encryption.AESEncryption(config.as[String]("encryption.secret"))
      else Encryption.NoEncryption
    }

    new InteractionManagerKubernetes(postTimeout, computationTimeout)(actorSystem, mat, encryption)
  }
}