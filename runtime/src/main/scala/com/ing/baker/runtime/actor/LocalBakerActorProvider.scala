package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import com.google.common.collect.Sets

import scala.collection.JavaConverters._
import scala.concurrent.duration.Duration

class LocalBakerActorProvider extends BakerActorProvider {

  override def createRecipeActors(recipeName: String, receivePeriod: Duration, petriNetActorProps: Props)(
      implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata) = {
    val recipeMetadata = new LocalRecipeMetadata(recipeName)
    val recipeManagerActor = actorSystem.actorOf(ActorIndex.props(petriNetActorProps, recipeMetadata, recipeName, receivePeriod), recipeName)

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
