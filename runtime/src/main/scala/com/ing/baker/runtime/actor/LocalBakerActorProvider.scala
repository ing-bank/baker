package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import com.ing.baker.runtime.actor.process_index.ProcessIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol.{GetIndex, Index}
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.core.interations.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.Future
import scala.concurrent.duration._

class LocalBakerActorProvider(config: Config) extends BakerActorProvider {

  private val retentionCheckInterval = config.as[Option[FiniteDuration]]("baker.actor.retention-check-interval").getOrElse(1 minute)
  private val configuredEncryption: Encryption = NoEncryption
  val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  override def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(
    implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(
      ProcessIndex.props(retentionCheckInterval, actorIdleTimeout, configuredEncryption, interactionManager, recipeManager))
  }

  override def createRecipeManagerActor()(implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(RecipeManager.props())
  }

  override def getIndex(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Future[Set[ActorMetadata]] = {

    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: akka.util.Timeout = timeout

    actorRef.ask(GetIndex).mapTo[Index].map(_.entries)
  }
}

