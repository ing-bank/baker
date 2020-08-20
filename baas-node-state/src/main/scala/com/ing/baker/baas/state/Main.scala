package com.ing.baker.baas.state

import java.io.File
import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.baas.interaction.BakeryHttp
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.typesafe.config.{Config, ConfigFactory}
import com.typesafe.scalalogging.LazyLogging
import javax.net.ssl.SSLContext
import kamon.Kamon
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import org.http4s.client.blaze.BlazeClientBuilder
import skuber.api.client.KubernetesClient

import scala.concurrent.ExecutionContext
import scala.util.{Failure, Success, Try}

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()


    val config = ConfigFactory.load(ConfigFactory.parseFile(new File("/bakery-config/application.conf")))

    val httpServerPort = config.getInt("baas-component.http-api-port")
    val recipeDirectory = config.getString("baas-component.recipe-directory")

    val interactionClientHttpsEnabled = config.getBoolean("baas-component.interaction-client.https-enabled")
    lazy val interactionClientKeystorePath = config.getString("baas-component.interaction-client.https-keystore-path")
    lazy val interactionClientKeystorePassword = config.getString("baas-component.interaction-client.https-keystore-password")
    lazy val interactionClientKeystoreType = config.getString("baas-component.interaction-client.https-keystore-type")

    val loggingEnabled = config.getBoolean("baas-component.api-logging-enabled")
    logger.info(s"Logging of API: ${loggingEnabled}  - MUST NEVER BE SET TO 'true' IN PRODUCTION")

    val eventSinkSettings = config.getConfig("baker.kafka-event-sink").as[KafkaEventSinkSettings]

    // Core dependencies
    implicit val system: ActorSystem =
      ActorSystem("BaaSStateNodeSystem", config)
    implicit val materializer: Materializer =
      ActorMaterializer()
    implicit val connectionPool: ExecutionContext =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())
    val hostname: InetSocketAddress =
      InetSocketAddress.createUnresolved("0.0.0.0", httpServerPort)
    val k8s: KubernetesClient = skuber.k8sInit

    val tlsConfig: Option[SSLContext] =
      if(interactionClientHttpsEnabled)
        Some(BakeryHttp.loadSSLContext(BakeryHttp.TLSConfig(
          password = interactionClientKeystorePassword,
          keystorePath = interactionClientKeystorePath,
          keystoreType = interactionClientKeystoreType
        )))
      else None

    val mainResource = for {
      interactionHttpClient <- BlazeClientBuilder[IO](connectionPool, tlsConfig).withCheckEndpointAuthentication(false).resource
      serviceDiscovery <- ServiceDiscovery.resource(interactionHttpClient, k8s)
      eventSink <- KafkaEventSink.resource(eventSinkSettings)
      baker = AkkaBaker
        .withConfig(AkkaBakerConfig(
          interactionManager = serviceDiscovery.buildInteractionManager,
          bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
          readJournal = AkkaBakerConfig.persistenceQueryFrom(config, system),
          timeouts = AkkaBakerConfig.Timeouts.from(config),
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config),
        )(system))
      _ <- Resource.liftF(eventSink.attach(baker))
      _ <- Resource.liftF(RecipeLoader.loadRecipesIntoBaker(recipeDirectory, baker))
      _ <- Resource.liftF(IO.async[Unit] { callback =>
        Cluster(system).registerOnMemberUp {
          callback(Right(()))
        }
      })
      _ <- StateNodeService.resource(baker, hostname, serviceDiscovery, loggingEnabled)
    } yield ()

    mainResource.use(_ => IO.never).as(ExitCode.Success)
  }
}
