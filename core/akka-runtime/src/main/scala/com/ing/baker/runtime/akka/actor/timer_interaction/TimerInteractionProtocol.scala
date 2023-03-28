package com.ing.baker.runtime.akka.actor.timer_interaction

import akka.actor.ActorRef
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.TransitionFiredEvent
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable

sealed trait TimerInteractionProtocol extends BakerSerializable

object TimerInteractionProtocol {

  case class StartTimerInteraction(transitionFiredEvent: TransitionFiredEvent, originalSender: ActorRef) extends TimerInteractionProtocol

  case class TimerInteractionFinished(transitionFiredEvent: TransitionFiredEvent) extends TimerInteractionProtocol
}
