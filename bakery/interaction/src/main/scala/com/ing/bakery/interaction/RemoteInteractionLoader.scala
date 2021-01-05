package com.ing.bakery.interaction

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.ExecutionContext

object RemoteInteractionLoader extends LazyLogging {

  def apply(implementations: List[InteractionInstance]): Unit = {
    val config = ConfigFactory.load()
    val port = config.getInt("interactions.http-api-port")
    val apiLoggingEnabled = config.getBoolean("interactions.api-logging-enabled")

//    val httpsEnabled = config.getBoolean("interactions.https-enabled")
//    val keystorePath = config.getString("interactions.interaction.https-keystore-path")
//    val keystorePassword = config.getString("interactions.interaction.https-keystore-password")
//    val keystoreType = config.getString("interactions.interaction.https-keystore-type")

    val healthServiceAddress = InetSocketAddress.createUnresolved("0.0.0.0", 9999)
    val address = InetSocketAddress.createUnresolved("0.0.0.0", port)
//    val tlsConfig =
//      if(httpsEnabled) Some(BakeryHttp.TLSConfig(password = keystorePassword, keystorePath = keystorePath, keystoreType = keystoreType))
//      else None

    implicit val executionContext: ExecutionContext = ExecutionContext.Implicits.global
    implicit val contextShift: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Timer[IO] = IO.timer(executionContext)

    RemoteInteractionService.resource(implementations, address, None /* todo tls config */, apiLoggingEnabled)
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