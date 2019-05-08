package com.ing.baker.runtime.core.actor

import akka.actor.{ActorRef, ActorSystem}
import akka.stream.Materializer
import com.ing.baker.runtime.core.actor.process_index.ProcessIndex
import com.ing.baker.runtime.core.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.core.actor.process_index.ProcessIndexProtocol.{GetIndex, Index}
import com.ing.baker.runtime.core.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.core.actor.serialization.Encryption
import com.ing.baker.runtime.core.internal.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.Await
import scala.concurrent.duration._

class LocalBakerActorProvider(config: Config, configuredEncryption: Encryption) extends BakerActorProvider {

  private val retentionCheckInterval = config.as[FiniteDuration]("baker.actor.retention-check-interval")
  private val ingredientsFilter: List[String] = config.as[List[String]]("baker.filtered-ingredient-values")

  val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  override def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(
    implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {

    actorSystem.actorOf(
      ProcessIndex.props(actorIdleTimeout, Some(retentionCheckInterval), configuredEncryption, interactionManager, recipeManager, ingredientsFilter))
  }

  override def createRecipeManagerActor()(implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {
    actorSystem.actorOf(RecipeManager.props())
  }

  override def getIndex(actorRef: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata] = {

    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: akka.util.Timeout = timeout

    val future = actorRef.ask(GetIndex).mapTo[Index].map(_.entries)

    Await.result(future, timeout)
  }
}

