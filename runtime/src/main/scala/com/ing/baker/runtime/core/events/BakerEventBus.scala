package com.ing.baker.runtime.core.events

import akka.actor.ActorRef
import akka.event.japi.SubchannelEventBus
import akka.util.Subclassification

class BakerEventBus extends SubchannelEventBus[BakerEvent, ActorRef, Class[_]] {

  override def subclassification: Subclassification[Class[_]] = new Subclassification[Class[_]] {
    override def isEqual(x: Class[_], y: Class[_]): Boolean = x.equals(y)
    override def isSubclass(x: Class[_], y: Class[_]): Boolean = x.isAssignableFrom(y)
  }

  override protected def classify(event: BakerEvent): Class[_] = event.getClass

  override protected def publish(event: BakerEvent, subscriber: ActorRef): Unit = subscriber ! event
}
