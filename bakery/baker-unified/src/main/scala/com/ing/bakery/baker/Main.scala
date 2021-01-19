package com.ing.bakery.baker

import akka.actor.{ActorSystem, Props}
import akka.cluster.Cluster
import cats.Id
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.bakery.metrics.MetricService
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.akka.internal.LocalInteractions
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.scaladsl.InteractionInstanceF
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.CollectorRegistry
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import org.http4s.Request
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.middleware.Metrics
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.Server
import org.springframework.context.annotation.AnnotationConfigApplicationContext
import skuber.LabelSelector
import skuber.api.client.KubernetesClient

import java.io.File
import java.net.InetSocketAddress
import java.util
import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext


object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))
    val bakerConfig = config.getConfig("baker")

    implicit val system: ActorSystem = ActorSystem("baker", config)
    implicit val executionContext: ExecutionContext = system.dispatcher

    system.actorOf(Props[ClusterEventWatch], name = "ClusterEventWatch")

    val httpServerPort = bakerConfig.getInt("api-port")
    val metricsPort = bakerConfig.getInt("metrics-port")
    val apiUrlPrefix = bakerConfig.getString("api-url-prefix")
    val loggingEnabled = bakerConfig.getBoolean("api-logging-enabled")
    logger.info(s"Logging of API: $loggingEnabled  - MUST NEVER BE SET TO 'true' IN PRODUCTION")

    val configurationClasses = bakerConfig.getStringList("interactions.local-configuration-classes")

    val eventSinkSettings = bakerConfig.getConfig("kafka-event-sink").as[KafkaEventSinkSettings]

    val interactions: List[InteractionInstanceF[IO]] = {
      if (configurationClasses.size() == 0) {
        logger.info("No interactions configured, probably interaction-configuration-classes config parameter is empty")
      }
      (configurationClasses.asScala map { configurationClass =>
        val configClass = Class.forName(configurationClass)
        val ctx = new AnnotationConfigApplicationContext()
        ctx.register(configClass)
        ctx.refresh()
        val interactionsAsJavaMap: util.Map[String, Interaction] =
          ctx.getBeansOfType(classOf[Interaction])
        val interactions = interactionsAsJavaMap
          .asScala
          .values
          .map(InteractionInstanceF.unsafeFrom[IO])
          .toList
        logger.info(s"Loaded ${interactions.size} interactions from $configurationClass: ${interactions.sortBy(_.name).map(_.name).mkString(",")}")
        interactions
      } toList).flatten
    }
    val localInteractions = LocalInteractions(interactions)

    logger.info("Starting Akka Baker...")

    val remoteInteractionCallContext: ExecutionContext = system.dispatchers.lookup("akka.actor.remote-interaction-dispatcher")

    val k8s: KubernetesClient = skuber.k8sInit

    def interactionRequestClassifier(request: Request[IO]): Option[String] = {
      // /api/bakery/interactions/<id>/execute - we take ID part we care most about
      val p = request.uri.path.split('/')
      if (p.length == 5) Some(p(4)) else None
    }

    val mainResource: Resource[IO, Server[IO]] =
      for {
        metrics <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")
        interactionHttpClient <- BlazeClientBuilder[IO](remoteInteractionCallContext, None) // todo SSL context
          .withCheckEndpointAuthentication(false)
          .resource
        eventSink <- KafkaEventSink.resource(eventSinkSettings)

        interactionDiscovery <- InteractionDiscovery.resource(
          Metrics[IO](metrics, interactionRequestClassifier)(interactionHttpClient),
          k8s,
          localInteractions,
          bakerConfig.getIntList("interactions.localhost-ports").asScala.map(_.toInt).toList,
          noneIfEmpty(bakerConfig.getString("interactions.pod-label-selector"))
            .map(_.split("="))
            .map { kv => LabelSelector(LabelSelector.IsEqualRequirement(kv(0), kv(1))) }
        )

        baker = AkkaBaker.withConfig(AkkaBakerConfig(
          interactions = interactionDiscovery,
          bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
          timeouts = AkkaBakerConfig.Timeouts.apply(config),
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config)
        )(system))

        _ <- Resource.liftF(eventSink.attach(baker))
        _ <- Resource.liftF(RecipeLoader.loadRecipesIntoBaker(configPath, baker))
        _ <- Resource.liftF(IO.async[Unit] { callback =>
          Cluster(system).registerOnMemberUp {
            logger.info("Akka cluster is now up")
            callback(Right(()))
          }
        })

        _ <- MetricService.resource(
          InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
        )

        bakerService <- BakerService.resource(baker,
          InetSocketAddress.createUnresolved("0.0.0.0", httpServerPort),
          apiUrlPrefix, interactionDiscovery, loggingEnabled)
      } yield bakerService

    mainResource.use( s => {
      logger.info(s"Bakery started at ${s.address}/${s.baseUri}, enabling the readiness in Akka management")
      BakerReadinessCheck.enable()
      IO.never
    }
    ).as(ExitCode.Success)
  }

  private def noneIfEmpty(str: String): Option[String] = if (str == null || str.isEmpty) None else Some(str)
}
