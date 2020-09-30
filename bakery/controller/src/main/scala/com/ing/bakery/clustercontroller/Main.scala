package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.bakery.clustercontroller.controllers.{BakerController, ComponentConfigController, InteractionController}
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import kamon.Kamon
import skuber.api.client.KubernetesClient

import scala.concurrent.ExecutionContext

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()

    val config = ConfigFactory.load()
    val useCrds = config.getBoolean("bakery-controller.use-crds")

    implicit val system: ActorSystem =
      ActorSystem("bakery-baker-system")
    val k8s: KubernetesClient =
      skuber.k8sInit
    implicit val connectionPool =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())
    val interactionMutualTLS: Option[MutualAuthKeystoreConfig] =
      MutualAuthKeystoreConfig.from(config, "interaction")
    val interactionClientMutualTLS: Option[MutualAuthKeystoreConfig] =
      MutualAuthKeystoreConfig.from(config, "interaction-client")

    interactionMutualTLS.foreach { config =>
      logger.info(s"Mutual TLS authentication enabled for interactions, using secret name ${config.secretName}")
    }
    interactionClientMutualTLS.foreach { config =>
      logger.info(s"Mutual TLS authentication enabled for interaction clients, using secret name ${config.secretName}")
    }

    (for {
      configCache <- ComponentConfigController.run(k8s)
      _ <- BakeryControllerService.resource(InetSocketAddress.createUnresolved("0.0.0.0", 8080))
      _ <- if(useCrds) InteractionController.run(k8s, connectionPool, interactionMutualTLS, interactionClientMutualTLS) else Resource.liftF(IO.unit)
      _ <- InteractionController.runFromConfigMaps(k8s, connectionPool, interactionMutualTLS, interactionClientMutualTLS)
      _ <- if(useCrds) BakerController.run(k8s, configCache, interactionClientMutualTLS) else Resource.liftF(IO.unit)
      _ <- BakerController.runFromConfigMaps(k8s, configCache, interactionClientMutualTLS)
    } yield ()).use(_ => IO.never).as(ExitCode.Success)
  }
}
