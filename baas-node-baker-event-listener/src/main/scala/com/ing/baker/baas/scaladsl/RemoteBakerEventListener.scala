package com.ing.baker.baas.scaladsl

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.bakerlistener.RemoteBakerEventListenerService
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.typesafe.config.ConfigFactory

import scala.concurrent.{ExecutionContext, Future}

object RemoteBakerEventListener extends common.RemoteBakerEventListener[Future] with ScalaApi {

  override type BakerEventType = BakerEvent

  override def load(listenerFunction: BakerEvent => Unit): Unit = {

    val config = ConfigFactory.load()
    val port = config.getInt("baas-component.http-api-port")

    val address = InetSocketAddress.createUnresolved("127.0.0.1", port)

    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.Implicits.global)
    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.Implicits.global)

    RemoteBakerEventListenerService
      .resource(listenerFunction, address)
      .use(_ => IO.never)
      .unsafeRunAsyncAndForget()
  }
}

