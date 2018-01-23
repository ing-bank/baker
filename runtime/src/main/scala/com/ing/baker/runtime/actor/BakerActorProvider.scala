package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import com.ing.baker.runtime.actor.processindex.ProcessInstanceStore
import com.ing.baker.runtime.core.interations.InteractionManager


trait BakerActorProvider extends {

  def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(implicit actorSystem: ActorSystem) : (ActorRef, ProcessInstanceStore)

  def createRecipeManagerActor()(implicit actorSystem: ActorSystem) : (ActorRef)
}
