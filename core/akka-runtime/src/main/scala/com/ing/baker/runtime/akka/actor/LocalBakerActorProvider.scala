package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import cats.effect.IO
import com.ing.baker.runtime.akka.AkkaBakerConfig
import com.ing.baker.runtime.akka.actor.process_index.{ProcessIndexActor, RecipeCache}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexActor.ActorMetadata
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{GetIndex, Index}
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.RecipeManager
import com.ing.baker.runtime.serialization.Encryption

import scala.concurrent.Await
import scala.concurrent.duration._

class LocalBakerActorProvider(
                               retentionCheckInterval: FiniteDuration,
                               ingredientsFilter: List[String],
                               actorIdleTimeout: Option[FiniteDuration],
                               configuredEncryption: Encryption,
                               timeouts: AkkaBakerConfig.Timeouts,
                             ) extends BakerActorProvider {
  override def initialize(implicit system: ActorSystem): Unit = Unit

  override def createProcessIndexActor(interactionManager: InteractionManager[IO], recipeCache: RecipeCache)(
    implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(
      ProcessIndexActor.props(
        recipeCache,
        actorIdleTimeout,
        Some(retentionCheckInterval),
        configuredEncryption,
        interactionManager,
        ingredientsFilter))
  }

  override def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata] = {
    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: akka.util.Timeout = timeout
    val future = actorRef.ask(GetIndex).mapTo[Index].map(_.entries)
    Await.result(future, timeout)
  }
}

