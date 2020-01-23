package com.ing.baker.baas.javadsl

import java.util.concurrent.CompletableFuture

import com.ing.baker.baas.common
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

object RemoteInteraction extends common.RemoteInteraction[CompletableFuture] with JavaApi {

  override type InteractionInstanceType = InteractionInstance

  override def load(implementation: InteractionInstance): Unit =
    scaladsl.RemoteInteraction.load(implementation.asScala)
}
