package com.ing.baker.runtime.akka.actor.timer_interaction

import akka.actor.{ActorLogging, Props, ReceiveTimeout}
import akka.persistence.{DeleteMessagesFailure, DeleteMessagesSuccess, PersistentActor}
import com.ing.baker.runtime.akka.actor.timer_interaction.TimerInteraction.prefix
import com.ing.baker.runtime.akka.actor.timer_interaction.TimerInteractionProtocol.StartTimerInteraction

object TimerInteraction {

  def prefix(id: String) = s"timer-interaction-$id-"

  def props() = Props(new TimerInteraction)
}

class TimerInteraction() extends PersistentActor with ActorLogging {

  override def receiveCommand: Receive = initialised

  override def preStart(): Unit = {
    log.info("TimerInteraction started")
  }

  override def postStop(): Unit = {
    log.info("TimerInteraction stopped")
  }

  override def receiveRecover: Receive = {
    case _ => ()
  }


  def initialised: Receive = {
    case StartTimerInteraction(transitionFiredEvent, originalSender) =>
      log.info(s"StartTimerInteraction received")
      sender().tell(transitionFiredEvent, originalSender)
      deleteMessages(lastSequenceNr)
      context.become(waitForDeleteConfirmation())
  }

  override def persistenceId: String = prefix(context.self.path.name)

  def waitForDeleteConfirmation(): Receive = {
    case DeleteMessagesSuccess(toSequenceNr) =>
      log.debug("TimerInteraction deletion success")
      context.stop(self)

    case DeleteMessagesFailure(cause, toSequenceNr) =>
      log.warning("TimerInteraction deletion failed")
      context.stop(self)

    case ReceiveTimeout =>
      log.warning(s"imerInteraction deletion timeout")
      context.stop(self)
  }
}
