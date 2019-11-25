package com.ing.baker.baas.javadsl

import java.util.concurrent.CompletableFuture
import java.util.function.BiConsumer

import akka.actor.ActorSystem
import com.ing.baker.baas.common
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.javadsl.{EventInstance, RecipeEventMetadata}

import scala.compat.java8.FutureConverters

class BaaSEventListener(actorSystem: ActorSystem) extends common.BaaSEventListener[CompletableFuture] with JavaApi {

  override type EventInstanceType = EventInstance

  override type RecipeEventMetadataType = RecipeEventMetadata

  override def registerEventListener(recipeName: String, listenerFunction: BiConsumer[RecipeEventMetadata, EventInstance]): CompletableFuture[Unit] =
    FutureConverters.toJava(scaladsl.BaaSEventListener(actorSystem).registerEventListener(recipeName, (metadata, event) => listenerFunction.accept(metadata.asJava, event.asJava))).toCompletableFuture
}
