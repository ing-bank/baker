package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import akka.stream.Materializer
import com.ing.baker.runtime.core.interations.InteractionManager

trait BakerActorProvider extends {

  def createBakerActor(interactionManager: InteractionManager)(implicit actorSystem: ActorSystem, materializer: Materializer) : ActorRef
}
