package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.bakery.clustercontroller.controllers.{BakerController, InteractionController, ForceRollingUpdateOnConfigMapUpdate}
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
    implicit val k8s: KubernetesClient =
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
      configWatch <- Resource.liftF(ForceRollingUpdateOnConfigMapUpdate.build)
      _ <- configWatch.runController
      _ <- BakeryControllerService.resource(InetSocketAddress.createUnresolved("0.0.0.0", 8080))
      _ <- if(useCrds) InteractionController.run(configWatch, connectionPool, interactionMutualTLS, interactionClientMutualTLS) else Resource.liftF(IO.unit)
      _ <- InteractionController.runFromConfigMaps(configWatch, connectionPool, interactionMutualTLS, interactionClientMutualTLS)
      _ <- if(useCrds) BakerController.run(configWatch, interactionClientMutualTLS) else Resource.liftF(IO.unit)
      _ <- BakerController.runFromConfigMaps(configWatch, interactionClientMutualTLS)
    } yield ()).use(_ => IO.never).as(ExitCode.Success)
  }
}
