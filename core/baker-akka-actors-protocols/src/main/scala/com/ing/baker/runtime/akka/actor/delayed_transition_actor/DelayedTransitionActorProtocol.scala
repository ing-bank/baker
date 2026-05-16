package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import akka.actor.ActorRef
import com.ing.baker.petrinet.api.{Id, Marking}
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable

sealed trait DelayedTransitionActorProtocol extends BakerSerializable

object DelayedTransitionActorProtocol {

  case class ScheduleDelayedTransition(recipeInstanceId: String, waitTimeInMillis: Long, jobId: Long, transitionId: Long, consumed: Marking[Id], eventToFire: String, originalSender: ActorRef) extends DelayedTransitionActorProtocol

  case object StartTimer extends DelayedTransitionActorProtocol

  case class FireDelayedTransition(recipeInstanceId: String, jobId: Long, transitionId: Long, eventToFire: String, originalSender: ActorRef) extends DelayedTransitionActorProtocol

  case class FireDelayedTransitionAck(recipeInstanceId: String, jobId: Long) extends DelayedTransitionActorProtocol

  case object TickTimer extends DelayedTransitionActorProtocol

  // Event sourcing data structures
  case class DelayedTransitionInstance(recipeInstanceId: String,
                                       timeToFire: Long,
                                       jobId: Long,
                                       transitionId: Long,
                                       eventToFire: String,
                                       optionalActorRef: Option[ActorRef]) extends BakerSerializable

  case class DelayedTransitionScheduled(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  case class DelayedTransitionExecuted(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  case class DelayedTransitionSnapshot(waitingTransitions: Map[String, DelayedTransitionInstance]) extends BakerSerializable
}
