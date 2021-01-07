package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import cats.effect.IO
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.model.InteractionsF

import scala.concurrent.duration.FiniteDuration

trait BakerActorProvider extends {

  def createProcessIndexActor(interactionManager: InteractionsF[IO], recipeManager: ActorRef)(implicit actorSystem: ActorSystem) : ActorRef

  def createRecipeManagerActor()(implicit actorSystem: ActorSystem) : ActorRef

  def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata]
}
