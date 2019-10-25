package com.ing.baker.baas.javadsl

import java.util.concurrent.CompletableFuture
import java.util.function.BiConsumer

import akka.actor.ActorSystem
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.javadsl.EventInstance

class BaaSEventListener(actorSystem: ActorSystem) extends common.BaaSEventListener[CompletableFuture] with JavaApi {

  override type EventInstanceType = EventInstance

  override def registerEventListener(recipeName: String, listenerFunction: BiConsumer[String, EventInstance]): CompletableFuture[Unit] = ???
}
