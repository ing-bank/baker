package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import akka.pattern.{BackoffOpts, BackoffSupervisor}
import cats.effect.IO
import com.ing.baker.runtime.akka.AkkaBakerConfig
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
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

  override def createProcessIndexActor(interactionManager: InteractionManager[IO], recipeManager: RecipeManager)(
    implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(
      BackoffSupervisor.props(
        BackoffOpts
          .onStop(
            ProcessIndex.props(
              actorIdleTimeout,
              Some(retentionCheckInterval),
              configuredEncryption,
              interactionManager,
              recipeManager,
              ingredientsFilter),
            childName = "ProcessIndexActor",
            minBackoff = 1 seconds,
            maxBackoff = 10 seconds,
            randomFactor = 0))
      )
  }

  override def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata] = {
    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: akka.util.Timeout = timeout
    val future = actorRef.ask(GetIndex).mapTo[Index].map(_.entries)
    Await.result(future, timeout)
  }
}

