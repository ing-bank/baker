package com.ing.baker.baas.scaladsl

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.common
import com.ing.baker.baas.recipelistener.RemoteEventListenerService
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.typesafe.config.ConfigFactory

import scala.concurrent.{ExecutionContext, Future}

object RemoteEventListener extends common.RemoteEventListener[Future] with ScalaApi {

  override type EventInstanceType = EventInstance

  override type RecipeEventMetadataType = RecipeEventMetadata

  override def load(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Unit = {
    val config = ConfigFactory.load()
    val port = config.getInt("baas-component.http-api-port")

    val address = InetSocketAddress.createUnresolved("0.0.0.0", port)

    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.Implicits.global)
    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.Implicits.global)

    RemoteEventListenerService
      .resource(listenerFunction, address)
      .use(_ => IO.never)
      .unsafeRunAsyncAndForget()
  }
}

