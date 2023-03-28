package com.ing.baker.runtime.akka.actor.timer_interaction

import akka.actor.{ActorLogging, Props}
import akka.persistence.PersistentActor
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.TransitionFiredEvent
import com.ing.baker.runtime.akka.actor.timer_interaction.TimerInteraction.prefix
import com.ing.baker.runtime.akka.actor.timer_interaction.TimerInteractionProtocol.{StartTimerInteraction, TimerInteractionFinished}

object TimerInteraction {

  def prefix(id: String) = s"timer-interaction-$id-"

  def props() = Props(new TimerInteraction)
}

class TimerInteraction() extends PersistentActor with ActorLogging {

  override def preStart(): Unit = {
    log.debug("TimerInteraction started")
  }

  override def postStop(): Unit = {
    log.debug("TimerInteraction stopped")
  }

  override def receiveRecover: Receive = {
    case _ => ()
  }

  override def receiveCommand: Receive = {
    case StartTimerInteraction(job, originalSender) => ()
//      sender ! TransitionFiredEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, producedMarking.marshall, out)
  }

  override def persistenceId: String = prefix(context.self.path.name)
}
