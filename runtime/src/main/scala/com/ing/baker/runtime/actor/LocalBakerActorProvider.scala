package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}

class LocalBakerActorProvider extends BakerActorProvider {

  override def createActorIndex(recipeName: String, petriNetActorProps: Props)(
      implicit actorSystem: ActorSystem): ActorRef = {
    actorSystem.actorOf(ActorIndex.props(petriNetActorProps), recipeName)
  }
}
