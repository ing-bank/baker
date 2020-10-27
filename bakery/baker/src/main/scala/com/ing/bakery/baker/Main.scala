package com.ing.bakery.baker

import java.io.File
import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.bakery.interaction.BakeryHttp
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import javax.net.ssl.SSLContext
import kamon.Kamon
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import org.http4s.client.blaze.BlazeClientBuilder
import skuber.api.client.KubernetesClient

import scala.concurrent.ExecutionContext

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()


    val config = ConfigFactory.load(ConfigFactory.parseFile(new File("/bakery-config/application.conf")))

    val httpServerPort = config.getInt("bakery-component.http-api-port")
    val recipeDirectory = config.getString("bakery-component.recipe-directory")

    implicit val system: ActorSystem = ActorSystem("baker", config)
    val hostname: InetSocketAddress = InetSocketAddress.createUnresolved("0.0.0.0", httpServerPort)

    val useRemoteInteractions = config.getBoolean("bakery-component.remote-interactions-enabled")

    val eventSinkSettings = config.getConfig("baker.kafka-event-sink").as[KafkaEventSinkSettings]
    val loggingEnabled = config.getBoolean("bakery-component.api-logging-enabled")
    logger.info(s"Logging of API: ${loggingEnabled}  - MUST NEVER BE SET TO 'true' IN PRODUCTION")

    val mainResource =
      if (useRemoteInteractions) {
        implicit val connectionPool: ExecutionContext = ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

        val interactionClientHttpsEnabled = config.getBoolean("bakery-component.interaction-client.https-enabled")
        lazy val interactionClientKeystorePath = config.getString("bakery-component.interaction-client.https-keystore-path")
        lazy val interactionClientKeystorePassword = config.getString("bakery-component.interaction-client.https-keystore-password")
        lazy val interactionClientKeystoreType = config.getString("bakery-component.interaction-client.https-keystore-type")
        lazy val scope = config.getString("bakery-component.interaction-client.scope")

        val k8s: KubernetesClient = skuber.k8sInit

        val tlsConfig: Option[SSLContext] =
          if (interactionClientHttpsEnabled)
            Some(BakeryHttp.loadSSLContext(BakeryHttp.TLSConfig(
              password = interactionClientKeystorePassword,
              keystorePath = interactionClientKeystorePath,
              keystoreType = interactionClientKeystoreType
            )))
          else None

        for {
          interactionHttpClient <- BlazeClientBuilder[IO](connectionPool, tlsConfig).withCheckEndpointAuthentication(false).resource
          serviceDiscovery <- RemoteInteractions.resource(interactionHttpClient, k8s, scope)
          eventSink <- KafkaEventSink.resource(eventSinkSettings)
          baker = AkkaBaker
            .withConfig(AkkaBakerConfig(
              interactions = serviceDiscovery.buildInteractionManager,
              bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
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
          _ <- BakerService.resource(baker, hostname, serviceDiscovery, loggingEnabled)
        } yield ()

      } else {
        for {
          eventSink <- KafkaEventSink.resource(eventSinkSettings)
          baker = AkkaBaker
            .withConfig(AkkaBakerConfig(
              interactions = initialiseBundledInteractions,
              bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
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
          _ <- BakerService.resource(baker, hostname, serviceDiscovery, loggingEnabled)
        } yield ()
      }

    mainResource.use(_ => {
      logger.info("Baker initalisation complete, enabling the readiness")
      BakerReadinessCheck.enable()
      IO.never}
    ).as(ExitCode.Success)
  }
}
