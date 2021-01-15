package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem}
import cats.effect.IO
import com.ing.baker.runtime.akka.AkkaBakerConfig
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{GetIndex, Index}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerActor
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.runtime.{RecipeManager, RecipeManagerActorImpl}

import scala.concurrent.Await
import scala.concurrent.duration._

class LocalBakerActorProvider(
                               retentionCheckInterval: FiniteDuration,
                               ingredientsFilter: List[String],
                               actorIdleTimeout: Option[FiniteDuration],
                               configuredEncryption: Encryption,
                               timeouts: AkkaBakerConfig.Timeouts
                             ) extends BakerActorProvider {

  override def createProcessIndexActor(interactionManager: InteractionsF[IO], recipeManager: RecipeManager)(
    implicit actorSystem: ActorSystem): ActorRef = {
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

  override def createRecipeManager()(implicit actorSystem: ActorSystem): RecipeManager = {
    import actorSystem.dispatcher

    new RecipeManagerActorImpl(
      actor = actorSystem.actorOf(RecipeManagerActor.props()),
      settings = RecipeManagerActorImpl.Settings(
        addRecipeTimeout = timeouts.defaultAddRecipeTimeout,
        inquireTimeout = timeouts.defaultInquireTimeout))
  }

  override def getAllProcessesMetadata(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata] = {
    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: akka.util.Timeout = timeout
    val future = actorRef.ask(GetIndex).mapTo[Index].map(_.entries)
    Await.result(future, timeout)
  }
}

