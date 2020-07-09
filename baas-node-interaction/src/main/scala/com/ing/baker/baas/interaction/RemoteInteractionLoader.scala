package com.ing.baker.baas.interaction

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory

import scala.concurrent.ExecutionContext

object RemoteInteractionLoader {

  def apply(implementations: List[InteractionInstance]): Unit = {
    val config = ConfigFactory.load()
    val port = config.getInt("baas-component.http-api-port")
    val httpsEnabled = config.getBoolean("baas-component.interaction.https-enabled")
    val keystorePath = config.getString("baas-component.interaction.https-keystore-path")
    val keystorePassword = config.getString("baas-component.interaction.https-keystore-password")
    val keystoreType = config.getString("baas-component.interaction.https-keystore-type")

    val address = InetSocketAddress.createUnresolved("0.0.0.0", port)
    val tlsConfig =
      if(httpsEnabled) Some(BakeryHttp.TLSConfig(password = keystorePassword, keystorePath = keystorePath, keystoreType = keystoreType))
      else None

    implicit val executionContext: ExecutionContext = ExecutionContext.Implicits.global
    implicit val contextShift: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Timer[IO] = IO.timer(executionContext)

    RemoteInteractionService.resource(implementations, address, tlsConfig)
      .flatMap(_ => HealthService.resource)
      .use(_ => IO.never)
      .unsafeRunAsyncAndForget()
  }
}
