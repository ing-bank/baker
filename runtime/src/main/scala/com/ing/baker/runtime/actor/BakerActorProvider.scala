package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import com.ing.baker.runtime.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.core.interations.InteractionManager

import scala.concurrent.Future
import scala.concurrent.duration.FiniteDuration


trait BakerActorProvider extends {

  def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(implicit actorSystem: ActorSystem) : ActorRef

  def createRecipeManagerActor()(implicit actorSystem: ActorSystem) : ActorRef

  def getIndex(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Future[Set[ActorMetadata]]
}
