package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import akka.actor.{ActorLogging, ActorRef, Props}
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActor.{DelayedTransitionExecuted, DelayedTransitionInstance, DelayedTransitionScheduled, getId, prefix}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol.{FireDelayedTransition, FireDelayedTransitionAck, ScheduleDelayedTransition, StartTimer, TickTimer}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{NoSuchProcess, ProcessDeleted}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable

import scala.collection.mutable
import scala.concurrent.duration.FiniteDuration

object DelayedTransitionActor {

  def prefix(id: String) = s"timer-interaction-$id-"

  def props(processIndex: ActorRef) = Props(new DelayedTransitionActor(processIndex: ActorRef))

  case class DelayedTransitionInstance(recipeInstanceId: String,
                                       timeToFire: Long,
                                       jobId: Long,
                                       transitionId: Long,
                                       eventToFire: String,
                                       optionalActorRef: Option[ActorRef]) extends BakerSerializable

  case class DelayedTransitionScheduled(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  case class DelayedTransitionExecuted(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  private def getId(recipeInstanceId: String, jobId: Long): String =
    recipeInstanceId + jobId
}

class DelayedTransitionActor(processIndex: ActorRef) extends PersistentActor with ActorLogging {

  private var waitingTimer: Map[String, DelayedTransitionInstance] = Map[String, DelayedTransitionInstance]()

  import context.dispatcher

  override def receiveCommand: Receive = starting

  override def preStart(): Unit = {
    log.debug(s"DelayedTransitionActor started: ${persistenceId}")
  }

  override def postStop(): Unit = {
    log.debug(s"DelayedTransitionActor stopped: ${persistenceId}")
  }

  private def handleScheduleDelayedTransition(event: ScheduleDelayedTransition) = {
    val id = getId(event.recipeInstanceId, event.jobId)
    val instance = DelayedTransitionInstance(
      event.recipeInstanceId,
      System.currentTimeMillis() + event.waitTimeInMillis,
      event.jobId,
      event.transitionId,
      event.eventToFire,
      Some(event.originalSender)
    )
    persist(DelayedTransitionScheduled(id, instance)) { _ =>
      if (!waitingTimer.contains(id)) {
        waitingTimer += (id -> instance)
        sender() ! ProcessInstanceProtocol.TransitionDelayed(event.jobId, event.transitionId, event.consumed)
      }
      else {
        log.warning(s"Ignoring ScheduleDelayedTransition since it already exists")
        sender() ! ProcessInstanceProtocol.TransitionDelayed(event.jobId, event.transitionId, event.consumed)
      }
    }
  }

  def starting: Receive = {
    case event@ScheduleDelayedTransition(recipeInstanceId, waitTimeInMillis, jobId, transitionId, consumed, eventToFire, originalSender) =>
      handleScheduleDelayedTransition(event)

    case StartTimer =>
      //TODO Make this configurable
      context.system.scheduler.scheduleAtFixedRate(FiniteDuration.apply(1, "seconds"), FiniteDuration.apply(1, "seconds"), context.self, TickTimer)
      context.become(running)
  }

  // TODO Do not grow indefinitely (Use snapshots/remove old entries)
  def running: Receive = {
    case event@ScheduleDelayedTransition(recipeInstanceId, waitTimeInMillis, jobId, transitionId, consumed, eventToFire, originalSender) =>
      handleScheduleDelayedTransition(event)

    case TickTimer =>
      waitingTimer.foreach { case (id, instance) =>
        if (System.currentTimeMillis() > instance.timeToFire) {
          processIndex ! FireDelayedTransition(instance.recipeInstanceId,
            instance.jobId,
            instance.transitionId,
            instance.eventToFire,
            instance.optionalActorRef.getOrElse(self))
        }
      }

    case FireDelayedTransitionAck(recipeInstanceId, jobId) =>
      val id = getId(recipeInstanceId, jobId)
      waitingTimer.get(id) match {
        case Some(instance) =>
          persist(DelayedTransitionExecuted(id, instance)) { _ =>
            waitingTimer -= id
          }
        case None => log.error(s"FireDelayedTransitionAck received for $id but not found")
      }

    case ProcessDeleted(recipeInstanceId) =>
      log.error(s"ProcessDeleted received in DelayedTransitionInstance for $recipeInstanceId")
      waitingTimer --= waitingTimer.filter(d => d._2.recipeInstanceId == recipeInstanceId).keys

    case NoSuchProcess(recipeInstanceId) =>
      log.error(s"NoSuchProcess received in DelayedTransitionInstance for $recipeInstanceId")
      waitingTimer --= waitingTimer.filter(d => d._2.recipeInstanceId == recipeInstanceId).keys
  }

  override def persistenceId: String = prefix(context.self.path.name)

  override def receiveRecover: Receive = {
    case scheduled: DelayedTransitionScheduled =>
      waitingTimer += (
        scheduled.id ->
        scheduled.delayedTransitionInstance)
    case fired: DelayedTransitionExecuted =>
      waitingTimer += (
        fired.id ->
        fired.delayedTransitionInstance)
  }
}
