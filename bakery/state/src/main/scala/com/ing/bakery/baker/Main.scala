package com.ing.bakery.baker

import cats.effect.{ExitCode, IO, IOApp}
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging

import java.io.File
import java.net.InetSocketAddress
import scala.concurrent.duration.Duration

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))
    val bakerConfig = config.getConfig("baker")
    val apiPort = bakerConfig.getInt("api-port")
    val metricsPort = bakerConfig.getInt("metrics-port")
    val apiUrlPrefix = bakerConfig.getString("api-url-prefix")
    val dashboardPath = bakerConfig.getString("dashboard-path")
    val loggingEnabled = bakerConfig.getBoolean("api-logging-enabled")

    (for {
      bakery <- Bakery.resource(None)
      _ <- MetricService.resource(InetSocketAddress.createUnresolved("0.0.0.0", metricsPort), bakery.executionContext)

      bakerService <- BakerService.resource(
        bakery.baker,
        bakery.executionContext,
        InetSocketAddress.createUnresolved("0.0.0.0", apiPort),
        apiUrlPrefix, dashboardPath, loggingEnabled)

    } yield (bakery, bakerService))
      .use { case (bakery, bakerService) =>
        logger.info(s"Bakery started at ${bakerService.address}/${bakerService.baseUri}, enabling the readiness in Akka management")
        BakerReadinessCheck.enable()
        RecipeLoader.pollRecipesUpdates(configPath, bakery,
          Duration.fromNanos(config.getDuration("baker.recipe-poll-interval").toNanos))

    }.as(ExitCode.Success)
  }

}
