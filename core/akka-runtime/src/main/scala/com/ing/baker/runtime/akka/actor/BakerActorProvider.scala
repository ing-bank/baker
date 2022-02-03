package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import cats.effect.IO
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexActor.ActorMetadata
import com.ing.baker.runtime.akka.actor.process_index.RecipeCache
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.RecipeManager

import scala.concurrent.duration.FiniteDuration

trait BakerActorProvider extends {

  def initialize(implicit system: ActorSystem): Unit

  def createProcessIndexActor(interactionManager: InteractionManager[IO], recipeCache: RecipeCache)(implicit actorSystem: ActorSystem) : ActorRef

  def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata]
}
