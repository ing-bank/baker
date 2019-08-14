package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import akka.stream.Materializer
import com.ing.baker.runtime.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.core.internal.InteractionManager

import scala.concurrent.duration.FiniteDuration

trait BakerActorProvider extends {

  def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(implicit actorSystem: ActorSystem, materializer: Materializer) : ActorRef

  def createRecipeManagerActor()(implicit actorSystem: ActorSystem, materializer: Materializer) : ActorRef

  def getIndex(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata]
}
