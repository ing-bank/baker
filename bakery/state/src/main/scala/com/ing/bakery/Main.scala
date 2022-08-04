package com.ing.bakery

import cats.effect.{ExitCode, IO, IOApp}
import com.ing.baker.http.DashboardConfiguration
import com.ing.baker.http.server.common.RecipeLoader
import com.ing.baker.http.server.scaladsl.Http4sBakerServer
import com.ing.bakery.components.BakerReadinessCheck
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
    val metricsPort = config.getInt("baker.metrics-port")

    (for {
      bakery <- Bakery.akkaBakery(Some(config))
      _ <- MetricService.resource(InetSocketAddress.createUnresolved("0.0.0.0", metricsPort), bakery.executionContext)

      bakerService <- Http4sBakerServer.resource(
        bakery.baker,
        bakery.executionContext,
        config)

    } yield (bakery, bakerService))
      .use { case (bakery, bakerService) =>
        logger.info(s"Bakery started at ${bakerService.address}/${bakerService.baseUri}, enabling the readiness in Akka management")
        BakerReadinessCheck.enable()
        RecipeLoader.pollRecipesUpdates(configPath, bakery.baker,
          Duration.fromNanos(config.getDuration("baker.recipe-poll-interval").toNanos))

      }.as(ExitCode.Success)
  }

}
