package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import akka.stream.Materializer
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{GetIndex, Index}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.akka.internal.InteractionManager

import scala.concurrent.Await
import scala.concurrent.duration._

class LocalBakerActorProvider(
    retentionCheckInterval: FiniteDuration,
    ingredientsFilter: List[String],
    actorIdleTimeout: Option[FiniteDuration],
    configuredEncryption: Encryption
  ) extends BakerActorProvider {

  override def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(
    implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {
    actorSystem.actorOf(
      ProcessIndex.props(
        actorIdleTimeout,
        Some(retentionCheckInterval),
        configuredEncryption,
        interactionManager,
        recipeManager,
        ingredientsFilter
      ))
  }

  override def createRecipeManagerActor()(implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {
    actorSystem.actorOf(RecipeManager.props())
  }

  override def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata] = {
    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: akka.util.Timeout = timeout
    val future = actorRef.ask(GetIndex).mapTo[Index].map(_.entries)
    Await.result(future, timeout)
  }
}

