package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import com.google.common.collect.Sets

import scala.collection.JavaConverters._

class LocalBakerActorProvider extends BakerActorProvider {

  override def createRecipeActors(recipeName: String, petriNetActorProps: Props)(
      implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata) = {
    val recipeMetadata = new LocalRecipeMetadata(recipeName)
    val recipeManagerActor = actorSystem.actorOf(ActorIndex.props(petriNetActorProps, recipeMetadata, recipeName), recipeName)

    (recipeManagerActor, recipeMetadata)
  }
}

class LocalRecipeMetadata(override val recipeName: String) extends RecipeMetadata {
  private val allProcessesMetadata = Sets.newConcurrentHashSet[ProcessMetadata]()

  override def getAllProcessMetadata: Set[ProcessMetadata] = allProcessesMetadata.asScala.toSet

  override def addNewProcessMetadata(processId: String, created: Long): Unit = {
    allProcessesMetadata.add(ProcessMetadata(processId, created))
  }
}
