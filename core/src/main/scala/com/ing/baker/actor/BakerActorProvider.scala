package com.ing.baker.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import com.ing.baker.api.ProcessMetadata

trait BakerActorProvider extends {
  def createRecipeActors(recipeName: String, petriNetActorProps: Props)(implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata)
}

trait RecipeMetadata {
  val recipeName: String
  def getAllProcessMetadata: Set[ProcessMetadata]
  def addNewProcessMetadata(name: String, created: Long): Unit
}
