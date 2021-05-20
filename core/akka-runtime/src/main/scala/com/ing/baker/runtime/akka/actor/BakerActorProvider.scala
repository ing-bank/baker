package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import cats.effect.IO
import com.ing.baker.runtime.RecipeManager
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.model.InteractionManager

import scala.concurrent.duration.FiniteDuration

trait BakerActorProvider extends {

  def createProcessIndexActor(interactionManager: InteractionManager[IO], recipeManager: RecipeManager)(implicit actorSystem: ActorSystem) : ActorRef

  def createRecipeManager()(implicit actorSystem: ActorSystem) : RecipeManager

  def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata]
}
