package com.ing.baker.baas.javadsl

import java.util.concurrent.CompletableFuture
import java.util.function.Consumer

import com.ing.baker.baas.{common, scaladsl}
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.javadsl.BakerEvent

object RemoteBakerEventListener extends common.RemoteBakerEventListener[CompletableFuture] with JavaApi {

  override type BakerEventType = BakerEvent

  override def load(listenerFunction: Consumer[BakerEvent]): Unit =
    scaladsl.RemoteBakerEventListener.load(event => listenerFunction.accept(event.asJava))
}
