package com.ing.baker.actor

import akka.actor.{ActorRef, ActorSystem, Props}

trait BakerActorProvider extends {

  def createActorIndex(recipeName: String, petriNetActorProps: Props, globalMetadataActor: ActorRef)(implicit actorSystem: ActorSystem): ActorRef

}
