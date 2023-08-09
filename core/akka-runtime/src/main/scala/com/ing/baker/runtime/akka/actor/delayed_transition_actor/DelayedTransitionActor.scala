package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import akka.actor.{ActorRef, Props}
import akka.persistence._
import akka.sensors.actor.PersistentActorMetrics
import com.ing.baker.runtime.akka.actor.BakerCleanup
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActor._
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{NoSuchProcess, ProcessDeleted}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable

import scala.concurrent.duration.FiniteDuration

object DelayedTransitionActor {

  def prefix(id: String) = s"timer-interaction-$id-"

  def props(processIndex: ActorRef,
            cleanup:  BakerCleanup,
            snapShotInterval: Int,
            snapshotCount: Int) = Props(new DelayedTransitionActor(processIndex, cleanup, snapShotInterval, snapshotCount))

  case class DelayedTransitionInstance(recipeInstanceId: String,
                                       timeToFire: Long,
                                       jobId: Long,
                                       transitionId: Long,
                                       eventToFire: String,
                                       optionalActorRef: Option[ActorRef]) extends BakerSerializable

  case class DelayedTransitionScheduled(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  case class DelayedTransitionExecuted(id: String, delayedTransitionInstance: DelayedTransitionInstance) extends BakerSerializable

  case class DelayedTransitionSnapshot(waitingTransitions: Map[String, DelayedTransitionInstance]) extends BakerSerializable

  private def getId(recipeInstanceId: String, jobId: Long): String =
    recipeInstanceId + jobId
}

class DelayedTransitionActor(processIndex: ActorRef,
                             cleanup: BakerCleanup,
                             snapShotInterval: Int,
                             snapshotCount: Int) extends PersistentActor with PersistentActorMetrics {

  private var waitingTransitions: Map[String, DelayedTransitionInstance] = Map[String, DelayedTransitionInstance]()

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
    persistWithSnapshot(DelayedTransitionScheduled(id, instance)) { _ =>
      if (!waitingTransitions.contains(id)) {
        waitingTransitions += (id -> instance)
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

  def running: Receive = {
    case SaveSnapshotSuccess(metadata) =>
      log.debug("Snapshot saved")
      cleanupSnapshots(metadata.persistenceId, snapshotCount)

    case SaveSnapshotFailure(_, _) =>
      log.error("Saving snapshot failed")

    case event@ScheduleDelayedTransition(recipeInstanceId, waitTimeInMillis, jobId, transitionId, consumed, eventToFire, originalSender) =>
      handleScheduleDelayedTransition(event)

    case TickTimer =>
      waitingTransitions.foreach { case (id, instance) =>
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
      waitingTransitions.get(id) match {
        case Some(instance) =>
          persistWithSnapshot(DelayedTransitionExecuted(id, instance)) { _ =>
            waitingTransitions -= id
          }
        case None => log.error(s"FireDelayedTransitionAck received for $id but not found")
      }

    case ProcessDeleted(recipeInstanceId) =>
      log.error(s"ProcessDeleted received in DelayedTransitionInstance for $recipeInstanceId")
      waitingTransitions --= waitingTransitions.filter(d => d._2.recipeInstanceId == recipeInstanceId).keys

    case NoSuchProcess(recipeInstanceId) =>
      log.error(s"NoSuchProcess received in DelayedTransitionInstance for $recipeInstanceId")
      waitingTransitions --= waitingTransitions.filter(d => d._2.recipeInstanceId == recipeInstanceId).keys
  }

  override def persistenceId: String = prefix(context.self.path.name)

  def persistWithSnapshot[A](event: A)(handler: A => Unit): Unit = {
    persist(event)(handler)
    if (lastSequenceNr % snapShotInterval == 0 && lastSequenceNr != 0) {
      log.debug("Writing Snapshots")
      saveSnapshot(DelayedTransitionSnapshot(waitingTransitions))
    }
  }

  def cleanupSnapshots(persistenceId: String, snapShotsToKeep: Int) : Unit = {
    cleanup.deleteEventsAndSnapshotBeforeSnapshot(persistenceId, snapShotsToKeep)
    log.debug("Snapshots cleaned")
  }

  override def receiveRecover: Receive = {

    case SnapshotOffer(_, delayedTransitionSnapshot: DelayedTransitionSnapshot) =>
      log.debug("Loading Snapshots")
      waitingTransitions = delayedTransitionSnapshot.waitingTransitions
    case SnapshotOffer(_, _) =>
      val message = "could not load snapshot because snapshot was not of type ProcessIndexSnapShot"
      log.error(message)
      throw new IllegalArgumentException(message)
    case scheduled: DelayedTransitionScheduled =>
      waitingTransitions += (
        scheduled.id ->
        scheduled.delayedTransitionInstance)
    case fired: DelayedTransitionExecuted =>
      waitingTransitions -= fired.id
  }
}
