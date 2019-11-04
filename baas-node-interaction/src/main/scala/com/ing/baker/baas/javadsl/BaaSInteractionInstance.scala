package com.ing.baker.baas.javadsl

import java.util.concurrent.CompletableFuture

import akka.actor.ActorSystem
import com.ing.baker.baas.protocol
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

class BaaSInteractionInstance(actorSystem: ActorSystem) extends protocol.BaaSInteractionInstance[CompletableFuture] with JavaApi {

  override type InteractionInstanceType = InteractionInstance

  override def load(implementation: InteractionInstance*): Unit =
    scaladsl.BaaSInteractionInstance(actorSystem).load(implementation.map(_.asScala): _*)
}
