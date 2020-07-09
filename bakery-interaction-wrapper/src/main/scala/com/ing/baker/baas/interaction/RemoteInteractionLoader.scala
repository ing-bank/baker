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

    val address = InetSocketAddress.createUnresolved("0.0.0.0", port)

    implicit val executionContext = ExecutionContext.Implicits.global
    implicit val contextShift: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Timer[IO] = IO.timer(executionContext)

    RemoteInteractionService
      .resource(implementations, address)
      .use(_ => IO.never)
      .unsafeRunAsyncAndForget()
  }
}
