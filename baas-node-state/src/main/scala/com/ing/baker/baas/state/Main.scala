package com.ing.baker.baas.state

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import cats.implicits._
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.typesafe.config.ConfigFactory
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import skuber.api.client.KubernetesClient

import scala.concurrent.ExecutionContext

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {
    // Config
    val config = ConfigFactory.load()

    val httpServerPort = config.getInt("baas-component.http-api-port")
    val recipeDirectory = config.getString("baas-component.recipe-directory")

//    val eventSinkSettings = config.getConfig("baker.kafka-event-sink").as[KafkaEventSinkSettings]

    // Core dependencies
    implicit val system: ActorSystem =
      ActorSystem("BaaSStateNodeSystem")
    implicit val materializer: Materializer =
      ActorMaterializer()
    val connectionPool: ExecutionContext =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())
    val hostname: InetSocketAddress =
      InetSocketAddress.createUnresolved("0.0.0.0", httpServerPort)
    val k8s: KubernetesClient = skuber.k8sInit

    val mainResource = for {
      serviceDiscovery <- ServiceDiscovery.resource(connectionPool, k8s)
//      eventSink <- KafkaEventSink.resource(eventSinkSettings)
      baker = AkkaBaker
        .withConfig(AkkaBakerConfig(
          interactionManager = serviceDiscovery.buildInteractionManager,
          bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
          readJournal = AkkaBakerConfig.persistenceQueryFrom(config, system),
          timeouts = AkkaBakerConfig.Timeouts.from(config),
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config),
        )(system))
//      _ <- Resource.liftF(eventSink.attach(baker))
      _ <- Resource.liftF(RecipeLoader.loadRecipesIntoBaker(recipeDirectory, baker))
      _ <- Resource.liftF(IO.async[Unit] { callback =>
        Cluster(system).registerOnMemberUp {
          callback(Right(()))
        }
      })
      _ <- StateNodeService.resource(baker, recipeDirectory, hostname, serviceDiscovery)
    } yield ()

    mainResource.use(_ => IO.never).as(ExitCode.Success)
  }
}
