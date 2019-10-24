package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import com.ing.baker.baas.akka.InteractionAgent
import com.ing.baker.baas.common
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

import scala.concurrent.Future

case class BaaSInteractionInstance(actorSystem: ActorSystem) extends common.BaaSInteractionInstance[Future] with JavaApi {

  override type InteractionInstanceType = InteractionInstance

  override def load(implementation: InteractionInstance*): Unit =
    implementation.foreach { implementation =>
      actorSystem.actorOf(InteractionAgent(implementation))
    }
}

