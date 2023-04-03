package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import akka.actor.{ActorLogging, ActorRef, Props}
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActor.{DelayedTransitionExecuted, DelayedTransitionInstance, DelayedTransitionScheduled, prefix}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol.{FireDelayedTransition, ScheduleDelayedTransition, StartTimer, TickTimer}
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
                                       fired: Boolean,
                                       optionalActorRef: Option[ActorRef]) extends BakerSerializable

  case class DelayedTransitionScheduled(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  case class DelayedTransitionExecuted(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable
}

class DelayedTransitionActor(processIndex: ActorRef) extends PersistentActor with ActorLogging {

  private val waitingTimer: mutable.Map[String, DelayedTransitionInstance] = mutable.Map[String, DelayedTransitionInstance]()

  import context.dispatcher

  override def receiveCommand: Receive = starting

  override def preStart(): Unit = {
    log.debug(s"DelayedTransitionActor started: ${persistenceId}")
  }

  override def postStop(): Unit = {
    log.debug(s"DelayedTransitionActor stopped: ${persistenceId}")
  }

  private def handleScheduleDelayedTransition(event: ScheduleDelayedTransition) = {
    val id = event.recipeInstanceId + event.jobId
    val instance = DelayedTransitionInstance(
      event.recipeInstanceId,
      System.currentTimeMillis() + event.waitTimeInMillis,
      event.jobId,
      event.transitionId,
      event.eventToFire,
      fired = false,
      Some(event.originalSender)
    )
    persist(DelayedTransitionScheduled(id, instance)) { _ =>
      if (!waitingTimer.contains(id)) {
        waitingTimer.put(id, instance)
        sender() ! ProcessInstanceProtocol.TransitionDelayed(event.jobId, event.transitionId, event.consumed)
      }
      else {
        log.warning(s"Ignoring ScheduleDelayedTransition since it already exists")
      }
    }
  }

  def starting: Receive = {
    case event@ScheduleDelayedTransition(recipeInstanceId, waitTimeInMillis, jobId, transitionId, consumed, eventToFire, originalSender) =>
      handleScheduleDelayedTransition(event)

    case StartTimer =>
      context.system.scheduler.scheduleAtFixedRate(FiniteDuration.apply(1, "seconds"), FiniteDuration.apply(1, "seconds"), context.self, TickTimer)
      context.become(running)
  }

  // TODO Do not grow indefinitely (Use snapshots/remove old entries)
  def running: Receive = {
    case event@ScheduleDelayedTransition(recipeInstanceId, waitTimeInMillis, jobId, transitionId, consumed, eventToFire, originalSender) =>
      handleScheduleDelayedTransition(event)

    case TickTimer =>
      waitingTimer.foreach { case (id, instance) =>
        val newInstance = instance.copy(fired = true)
        if(!instance.fired &&  System.currentTimeMillis() > instance.timeToFire) {
          persist(DelayedTransitionExecuted(id, newInstance)) { _ =>
            processIndex ! FireDelayedTransition(instance.recipeInstanceId,
              instance.jobId,
              instance.transitionId,
              instance.eventToFire,
              instance.optionalActorRef.getOrElse(self))
            waitingTimer.put(id, newInstance)
          }
        }
      }
  }

  override def persistenceId: String = prefix(context.self.path.name)

  override def receiveRecover: Receive = {
    case scheduled: DelayedTransitionScheduled =>
      waitingTimer.put(
        scheduled.id,
        scheduled.delayedTransitionInstance)
    case fired: DelayedTransitionExecuted =>
      waitingTimer.put(
        fired.id,
        fired.delayedTransitionInstance)
  }
}
