package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}

trait BakerActorProvider extends {

  def createActorIndex(recipeName: String, petriNetActorProps: Props)(implicit actorSystem: ActorSystem): ActorRef

}
