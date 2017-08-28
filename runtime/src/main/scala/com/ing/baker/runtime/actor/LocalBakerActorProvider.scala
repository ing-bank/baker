package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import com.ing.baker.il.CompiledRecipe
import com.typesafe.config.Config

import net.ceedubs.ficus.Ficus._
import scala.concurrent.duration._

class LocalBakerActorProvider(config: Config) extends BakerActorProvider {

  private val retentionCheckInterval = config.as[Option[FiniteDuration]]("baker.actor.retention-check-interval").getOrElse(1 minute)

  override def createRecipeActors(recipe: CompiledRecipe, petriNetActorProps: Props)(
      implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata) = {
    val recipeMetadata = new LocalRecipeMetadata(recipe.name)
    val recipeManagerActor = actorSystem.actorOf(
      ProcessIndex.props(petriNetActorProps, recipeMetadata, recipe.name, recipe.eventReceivePeriod, recipe.retentionPeriod, retentionCheckInterval), recipe.name)

    (recipeManagerActor, recipeMetadata)
  }
}

