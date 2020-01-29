package com.ing.baker.baas.javadsl

import java.util.concurrent.CompletableFuture
import java.util.function.BiConsumer

import akka.actor.ActorSystem
import com.ing.baker.baas.common
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.javadsl.{EventInstance, RecipeEventMetadata}

import scala.compat.java8.FutureConverters

object RemoteEventListener extends common.RemoteEventListener[CompletableFuture] with JavaApi {

  override type EventInstanceType = EventInstance

  override type RecipeEventMetadataType = RecipeEventMetadata

  override def load(listenerFunction: BiConsumer[RecipeEventMetadata, EventInstance]): Unit =
    scaladsl.RemoteEventListener.load((metadata, event) => listenerFunction.accept(metadata.asJava, event.asJava))
}
