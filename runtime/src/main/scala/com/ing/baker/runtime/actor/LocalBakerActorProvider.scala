package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import com.ing.baker.runtime.actor.process_index.{LocalProcessInstanceStore, ProcessIndex, ProcessInstanceStore}
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.core.interations.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration._

class LocalBakerActorProvider(config: Config) extends BakerActorProvider {

  private val retentionCheckInterval = config.as[Option[FiniteDuration]]("baker.actor.retention-check-interval").getOrElse(1 minute)
  private val distributedProcessMetadataEnabled = false
  private val configuredEncryption: Encryption = NoEncryption
  val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  override def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(
    implicit actorSystem: ActorSystem): (ActorRef, ProcessInstanceStore) = {
    val processInstanceStore = new LocalProcessInstanceStore()
    val recipeManagerActor = actorSystem.actorOf(
      ProcessIndex.props(processInstanceStore, retentionCheckInterval, actorIdleTimeout, configuredEncryption, interactionManager, recipeManager))
    (recipeManagerActor, processInstanceStore)
  }

  override def createRecipeManagerActor()(implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(RecipeManager.props())
  }
}

