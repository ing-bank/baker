package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.CollectorRegistry
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.Server

import java.io.File
import java.net.InetSocketAddress
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

    if (production && loggingEnabled) {
      logger.error("Logging of API is enabled, but not allowed in production - stopping JVM")
      System.exit(1)
    }

    logger.info("Starting Akka Baker...")
    val mainResource: Resource[IO, (Server[IO], AkkaBaker, RecipeCache)] =
      for {
        maybeCassandra <- Cassandra.resource(config, system)
        _ <- Watcher.resource(config, system, maybeCassandra)
        _ <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")
        eventSink <- EventSink.resource(config)
        interactions <- InteractionRegistry.resource(config, system)
        baker = AkkaBaker.withConfig(AkkaBakerConfig(
          interactions = interactions,
          bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
          timeouts = AkkaBakerConfig.Timeouts.apply(config),
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config)
        )(system))
        _ <- Resource.eval(eventSink.attach(baker))
        recipeCache <- RecipeCache.resource(config, system, maybeCassandra)
        _ <- Resource.eval(RecipeLoader.loadRecipesIntoBaker(configPath, recipeCache, baker))
        _ <- Resource.eval(IO.async_[Unit] { callback =>
          //If using local Baker the registerOnMemberUp is never called, should onl be used during local testing.
          if (bakerConfig.getString("actor.provider") == "local")
            callback(Right(()))
          else
            Cluster(system).registerOnMemberUp {
              logger.info("Akka cluster is now up")
              callback(Right(()))
            }
        })

        _ <- MetricService.resource(InetSocketAddress.createUnresolved("0.0.0.0", metricsPort))

        bakerService <- BakerService.resource(baker,
          InetSocketAddress.createUnresolved("0.0.0.0", apiPort),
          apiUrlPrefix, dashboardPath, loggingEnabled)
      } yield (bakerService, baker, recipeCache)

    mainResource.use {
      case (s, baker, recipeCache) =>
        logger.info(s"Bakery started at ${s.address}/${s.baseUri}, enabling the readiness in Akka management")
        BakerReadinessCheck.enable()
        RecipeLoader.pollRecipesUpdates(configPath, recipeCache, baker,
          Duration.fromNanos(config.getDuration("baker.recipe-poll-interval").toNanos))
    }.as(ExitCode.Success)
  }


}
