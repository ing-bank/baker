package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import com.ing.baker.baas.akka.InteractionAgent
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.concurrent.Future

case class BaaSInteractionInstance(actorSystem: ActorSystem) extends common.BaaSInteractionInstance[Future] with ScalaApi {

  override type InteractionInstanceType = InteractionInstance

  override def load(implementation: InteractionInstance*): Unit =
    implementation.foreach { implementation =>
      actorSystem.actorOf(InteractionAgent(implementation))
    }
}

