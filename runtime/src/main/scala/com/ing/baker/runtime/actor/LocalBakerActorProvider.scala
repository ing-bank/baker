package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import com.ing.baker.il.CompiledRecipe

class LocalBakerActorProvider extends BakerActorProvider {

  override def createRecipeActors(recipe: CompiledRecipe, petriNetActorProps: Props)(
      implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata) = {
    val recipeMetadata = new LocalRecipeMetadata(recipe.name)
    val recipeManagerActor = actorSystem.actorOf(ProcessIndex.props(petriNetActorProps, recipeMetadata, recipe.name, recipe.eventReceivePeriod, recipe.retentionPeriod), recipe.name)

    (recipeManagerActor, recipeMetadata)
  }
}

