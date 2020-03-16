package com.ing.baker.baas.scaladsl

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.common
import com.ing.baker.baas.interaction.RemoteInteractionService
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory

import scala.concurrent.{ExecutionContext, Future}

object RemoteInteraction extends common.RemoteInteraction[Future] with ScalaApi {

  override type InteractionInstanceType = InteractionInstance

  override def load(implementation: InteractionInstance): Unit = {
    val config = ConfigFactory.load()
    val port = config.getInt("baas-component.http-api-port")

    val address = InetSocketAddress.createUnresolved("127.0.0.1", port)

    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.Implicits.global)
    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.Implicits.global)

    RemoteInteractionService
      .resource(implementation, address)
      .use(_ => IO.never)
      .unsafeRunAsyncAndForget()
  }
}
