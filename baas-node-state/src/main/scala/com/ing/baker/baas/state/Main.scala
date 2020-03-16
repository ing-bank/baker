package com.ing.baker.baas.state

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import cats.implicits._
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.scaladsl.Baker
import com.typesafe.config.ConfigFactory
import skuber.api.client.KubernetesClient

import scala.concurrent.ExecutionContext

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {
    // Config
    val config = ConfigFactory.load()
    val httpServerPort = config.getInt("baas-component.http-api-port")
    val namespace = config.getString("baas-component.kubernetes-namespace")

    // Core dependencies
    implicit val system: ActorSystem =
      ActorSystem("BaaSStateNodeSystem")
    implicit val materializer: Materializer =
      ActorMaterializer()
    val connectionPool: ExecutionContext =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())
    val hostname: InetSocketAddress =
      InetSocketAddress.createUnresolved("127.0.0.1", httpServerPort)
    val k8s: KubernetesClient = skuber.k8sInit

    val mainResource = for {
      serviceDiscovery <- ServiceDiscovery.resource(connectionPool, k8s)
      baker: Baker = AkkaBaker.withConfig(AkkaBakerConfig(
          interactionManager = serviceDiscovery.buildInteractionManager,
          bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
          readJournal = AkkaBakerConfig.persistenceQueryFrom(config, system),
          timeouts = AkkaBakerConfig.Timeouts.from(config),
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config)
        )(system))
      _ <- Resource.liftF(IO.async[Unit] { callback =>
        Cluster(system).registerOnMemberUp {
          callback(Right(()))
        }
      })
      _ <- Resource.liftF(serviceDiscovery.plugBakerEventListeners(baker))
      _ <- StateNodeService.resource(baker, hostname)
    } yield ()

    mainResource.use(_ => IO.never).as(ExitCode.Success)
  }
}
