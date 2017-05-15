package com.ing.baker.actor

import akka.actor.{ActorRef, ActorSystem, Props}

class LocalBakerActorProvider extends BakerActorProvider {

  override def createActorIndex(recipeName: String, petriNetActorProps: Props, globalMetadataActor: ActorRef)(
      implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(ActorIndex.props(petriNetActorProps, globalMetadataActor), recipeName)
  }
}
