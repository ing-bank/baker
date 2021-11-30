package com.ing.bakery.interaction

import java.net.InetSocketAddress

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.ExecutionContext
import cats.effect.Temporal

object RemoteInteractionLoader extends LazyLogging {

  def apply(implementations: List[InteractionInstance]): Unit = {
    val config = ConfigFactory.load()
    val port = config.getInt("baker.interactions.http-api-port")
    val metricsPort = config.getInt("baker.interactions.metrics-port")
    val metricsEnabled = config.getBoolean("baker.interactions.metrics-enabled")
    val apiUrlPrefix = config.getString("baker.interactions.api-url-prefix")
    val apiLoggingEnabled = config.getBoolean("baker.interactions.api-logging-enabled")
    val interactionPerTypeMetricsEnabled = config.getBoolean("baker.interactions.per-type-metrics-enabled")
    val httpsEnabled = config.getBoolean("baker.interactions.https-enabled")
    val keystorePath = config.getString("baker.interactions.https-keystore-path")
    val keystorePassword = config.getString("baker.interactions.https-keystore-password")
    val keystoreType = config.getString("baker.interactions.https-keystore-type")

    val healthServiceAddress = InetSocketAddress.createUnresolved("0.0.0.0", 9999)
    val address = InetSocketAddress.createUnresolved("0.0.0.0", port)
    val tlsConfig =
      if (httpsEnabled) Some(BakeryHttp.TLSConfig(password = keystorePassword, keystorePath = keystorePath, keystoreType = keystoreType))
      else None

    implicit val executionContext: ExecutionContext = ExecutionContext.Implicits.global
    implicit val contextShift: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Temporal[IO] = IO.timer(executionContext)

    RemoteInteractionService.resource(implementations, address, tlsConfig, apiLoggingEnabled,
      interactionPerTypeMetricsEnabled, metricsPort, metricsEnabled, apiUrlPrefix)
      .use(_ => {
        logger.info(s"Interactions started successfully at $address, now starting health service $healthServiceAddress")
        HealthService.resource(healthServiceAddress)
          .use(_ => IO.never)
          .unsafeRunAsyncAndForget()
        IO.never
      })
      .unsafeRunAsyncAndForget()
  }
}
