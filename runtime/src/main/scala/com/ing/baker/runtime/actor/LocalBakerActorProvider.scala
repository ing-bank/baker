package com.ing.baker.runtime.actor

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.stream.Materializer
import com.ing.baker.runtime.actor.process_index.ProcessIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol.ProcessIndexMessage
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol.RecipeManagerMessage
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.core.interations.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration._

class LocalBakerActor(processIndex: ActorRef, recipeManager: ActorRef) extends Actor {

  override def receive: Receive = {
    case msg: ProcessIndexMessage  => processIndex.forward(msg)
    case msg: RecipeManagerMessage => recipeManager.forward(msg)
  }
}

class LocalBakerActorProvider(config: Config, configuredEncryption: Encryption) extends BakerActorProvider {

  private val retentionCheckInterval = config.as[Option[FiniteDuration]]("baker.actor.retention-check-interval").getOrElse(1 minute)
  val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  override def createBakerActor(interactionManager: InteractionManager)(implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {
    val recipeManager = actorSystem.actorOf(RecipeManager.props())

    val processIndex = actorSystem.actorOf(
      ProcessIndex.props(retentionCheckInterval, actorIdleTimeout, configuredEncryption, interactionManager, recipeManager))

    actorSystem.actorOf(Props(new LocalBakerActor(processIndex, recipeManager)))
  }
}

