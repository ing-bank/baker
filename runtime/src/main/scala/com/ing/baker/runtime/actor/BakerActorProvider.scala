package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import com.ing.baker.il.CompiledRecipe


trait BakerActorProvider extends {

  def createRecipeActors(recipe: CompiledRecipe, petriNetActorProps: Props)(implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata)
}

