package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.akka.internal.CachedInteractionManager
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.CollectorRegistry
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.Server
import org.springframework.context.annotation.AnnotationConfigApplicationContext
import skuber.LabelSelector
import java.io.File
import java.net.InetSocketAddress
import java.util

import com.ing.baker.runtime.model.InteractionInstance

import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration.Duration


object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))
    val bakerConfig = config.getConfig("baker")

    implicit val system: ActorSystem = ActorSystem("baker", config)
    implicit val executionContext: ExecutionContext = system.dispatcher

    val apiPort = bakerConfig.getInt("api-port")
    val metricsPort = bakerConfig.getInt("metrics-port")
    val apiUrlPrefix = bakerConfig.getString("api-url-prefix")
    val dashboardPath = bakerConfig.getString("dashboard-path")
    val production = bakerConfig.getBoolean("production-safe-mode")
    val loggingEnabled = bakerConfig.getBoolean("api-logging-enabled")

    val allowSupersetForOutputTypes= bakerConfig.getOrElse[Boolean]("interaction-manager.allowSupersetForOutputTypes", false)

    if (production && loggingEnabled) {
      logger.error("Logging of API is enabled, but not allowed in production - stopping JVM")
      System.exit(1)
    }

    val configurationClasses = bakerConfig.getStringList("interactions.local-configuration-classes")

    val eventSinkSettings = bakerConfig.getConfig("event-sink")

    val pollInterval = Duration.fromNanos(config.getDuration("baker.recipe-poll-interval").toNanos)

    val interactions: List[InteractionInstance[IO]] = {
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
          .map(InteractionInstance.unsafeFrom[IO])
          .toList
        logger.info(s"Loaded ${interactions.size} interactions from $configurationClass: ${interactions.sortBy(_.name).map(_.name).mkString(",")}")
        interactions
      } toList).flatten
    }
    val interactionManager = CachedInteractionManager(interactions, allowSupersetForOutputTypes)

    logger.info("Starting Akka Baker...")

    val remoteInteractionCallContext: ExecutionContext = system.dispatchers.lookup("akka.actor.remote-interaction-dispatcher")

    val mainResource: Resource[IO, (Server[IO], AkkaBaker)] =
      for {
        _ <- Watcher.resource(config, system)
        _ <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")
        interactionHttpClient <- BlazeClientBuilder[IO](remoteInteractionCallContext, None) // todo SSL context
          .withCheckEndpointAuthentication(false)
          .resource
        eventSink <- EventSink.resource(eventSinkSettings)

        interactionDiscovery <- InteractionDiscovery.resource(
          interactionHttpClient,
          skuber.k8sInit,
          interactionManager,
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

        _ <- Resource.eval(eventSink.attach(baker))
        _ <- Resource.eval(RecipeLoader.loadRecipesIntoBaker(configPath, baker))
        _ <- Resource.eval(IO.async[Unit] { callback =>
          //If using local Baker the registerOnMemberUp is never called, should onl be used during local testing.
          if (bakerConfig.getString("actor.provider") == "local")
            callback(Right(()))
          else
            Cluster(system).registerOnMemberUp {
              logger.info("Akka cluster is now up")
              callback(Right(()))
            }
        })

        _ <- MetricService.resource(
          InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
        )

        bakerService <- BakerService.resource(baker,
          InetSocketAddress.createUnresolved("0.0.0.0", apiPort),
          apiUrlPrefix, dashboardPath, interactionDiscovery, loggingEnabled)
      } yield (bakerService, baker)

    mainResource.use {
      case (s, baker) => {
        logger.info(s"Bakery started at ${s.address}/${s.baseUri}, enabling the readiness in Akka management")
        BakerReadinessCheck.enable()
        RecipeLoader.pollRecipesUpdates(configPath, baker, pollInterval)
      }
    }.as(ExitCode.Success)
  }

  private def noneIfEmpty(str: String): Option[String] = if (str == null || str.isEmpty) None else Some(str)
}
