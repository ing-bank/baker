package com.ing.baker.baas.akka

import akka.actor.{Actor, ActorRef, Props}
import akka.cluster.pubsub.{DistributedPubSub, DistributedPubSubMediator}
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.scaladsl.EventInstance

object EventListenerAgent {

  case object CommitTimeout

  def apply(recipeName: String, listenerFunction: (String, EventInstance) => Unit): Props =
    Props(new EventListenerAgent(recipeName, listenerFunction))
}

class EventListenerAgent(recipeName: String, listenerFunction: (String, EventInstance) => Unit) extends Actor {

  val mediator: ActorRef =
    DistributedPubSub(context.system).mediator

  val eventsTopic: String =
    ProtocolDistributedEventPublishing.eventsTopic(recipeName)

  def subscribeToEvents(): Unit =
    mediator ! DistributedPubSubMediator.Subscribe(eventsTopic, self)

  def unsubscribeToEvents(): Unit =
    mediator ! DistributedPubSubMediator.Unsubscribe(eventsTopic, self)

  def receive: Receive = {
    case ProtocolDistributedEventPublishing.Event(recipeInstanceId, event) =>
      listenerFunction(recipeInstanceId, event)
  }
}
