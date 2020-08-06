package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.bakery.clustercontroller.controllers.{BakerController, BakerResource, InteractionController, InteractionResource}
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import kamon.Kamon
import skuber.api.client.KubernetesClient
import skuber.json.format.configMapFmt

import scala.concurrent.ExecutionContext

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()

    val config = ConfigFactory.load()
    val useCrds = config.getBoolean("bakery-controller.use-crds")

    implicit val system: ActorSystem =
      ActorSystem("bakery-baker-system")
    implicit val materializer: Materializer =
      ActorMaterializer()
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
      _ <- BakeryControllerService.resource(InetSocketAddress.createUnresolved("0.0.0.0", 8080))
      interactions = new InteractionController(connectionPool, interactionMutualTLS, interactionClientMutualTLS)
      bakers = new BakerController(interactionClientMutualTLS)
      _ <- if(useCrds) interactions.watch(k8s) else Resource.liftF(IO.unit)
      _ <- interactions.fromConfigMaps(InteractionResource.fromConfigMap).watch(k8s, label = Some("custom-resource-definition" -> "interactions"))
      _ <- if(useCrds) bakers.watch(k8s) else Resource.liftF(IO.unit)
      _ <- bakers.fromConfigMaps(BakerResource.fromConfigMap).watch(k8s, label = Some("custom-resource-definition" -> "bakers"))
    } yield ()).use(_ => IO.never).as(ExitCode.Success)
  }
}
