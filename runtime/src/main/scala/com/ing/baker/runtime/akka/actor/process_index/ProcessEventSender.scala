package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{Actor, ActorRef, Props, ReceiveTimeout}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.{RuntimeEvent, SensoryEventResult}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{FireSensoryEventReaction, ProcessEvent, FireSensoryEventRejection}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.events.{EventReceived, EventRejected, RejectReason}
import com.ing.baker.runtime.common.SensoryEventStatus
import org.slf4j.{Logger, LoggerFactory}

import scala.concurrent.duration.FiniteDuration

object ProcessEventSender {

  def apply(receiver: ActorRef, command: ProcessEvent): Props =
    Props(new ProcessEventSender(receiver, command))
}

/**
  * An actor that pushes all received messages on the process instance side to the node which requested a process event operation.
  * It's main usage is the publishing of events to the system event stream and logging message throughput.
  */
class ProcessEventSender(receiver: ActorRef, command: ProcessEvent) extends Actor {

  context.setReceiveTimeout(command.timeout)

  val log: Logger = LoggerFactory.getLogger(classOf[ProcessEventSender])

  val waitForRetries: Boolean = command.reaction match {
    case FireSensoryEventReaction.NotifyWhenReceived => false
    case FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries0) => waitForRetries0
    case FireSensoryEventReaction.NotifyBoth(waitForRetries0, _) => waitForRetries0
  }

  def notifyReceive(recipe: CompiledRecipe): Unit = {
    context.system.eventStream.publish(
      EventReceived(
        System.currentTimeMillis(),
        recipe.name,
        recipe.recipeId,
        command.processId,
        command.correlationId,
        command.event))
    command.reaction match {
      case FireSensoryEventReaction.NotifyWhenCompleted(_) =>
        ()
      case FireSensoryEventReaction.NotifyWhenReceived =>
        receiver ! SensoryEventStatus.Received
      case FireSensoryEventReaction.NotifyBoth(_, _) =>
        receiver ! SensoryEventStatus.Received
    }
  }

  def notifyComplete(cache: List[Any]): Unit = {
    lazy val runtimeEvents = cache.flatMap {
      case fired: TransitionFired => Some(fired.output.asInstanceOf[RuntimeEvent])
      case _ => None
    }
    lazy val result = SensoryEventResult(
      status = SensoryEventStatus.Completed,
      events = runtimeEvents.map(_.name),
      ingredients = runtimeEvents.flatMap(_.providedIngredients).toMap
    )
    command.reaction match {
      case FireSensoryEventReaction.NotifyWhenReceived =>
        ()
      case FireSensoryEventReaction.NotifyWhenCompleted(_) =>
        receiver ! result
      case FireSensoryEventReaction.NotifyBoth(_, alternativeReceiver) =>
        alternativeReceiver ! result
    }
    stopActor()
  }

  def rejectWith(rejection: FireSensoryEventRejection): Unit = {
    log.debug("Stopping ProcessEventSender and rejecting queue")
    log.debug("Reject reason: " + rejection.asReason)
    log.debug("message: " + rejection)
    context.system.eventStream.publish(
      EventRejected(
        System.currentTimeMillis(),
        command.processId,
        command.correlationId,
        command.event,
        rejection.asReason))
    command.reaction match {
      case FireSensoryEventReaction.NotifyBoth(_, completeReceiver) =>
        receiver ! rejection; completeReceiver ! rejection
      case FireSensoryEventReaction.NotifyWhenCompleted(_) =>
        receiver ! rejection
      case FireSensoryEventReaction.NotifyWhenReceived =>
        receiver ! rejection
    }
    stopActor()
  }

  def stopActor(): Unit = {
    log.debug("Stopping the ProcessEventSender")
    context.stop(self)
  }

  def handleRejections: Receive = {
    case rejection: ProcessInstanceProtocol.TransitionNotEnabled =>
      throw new IllegalArgumentException(s"IMMINENT BUG: $rejection should be transformed into a FiringLimitMet rejection")
    case rejection: ProcessInstanceProtocol.AlreadyReceived ⇒
      throw new IllegalArgumentException(s"IMMINENT BUG: $rejection should be transformed into a AlreadyReceived rejection")
    case rejection: ProcessInstanceProtocol.Uninitialized ⇒
      throw new IllegalArgumentException(s"IMMINENT BUG: $rejection should be transformed into a NoSuchProcess rejection")
    case rejection: FireSensoryEventRejection =>
      rejectWith(rejection)
  }

  def receive: Receive =
    handleRejections orElse {
      case recipe: CompiledRecipe =>
        context.become(waitForFirstEvent(recipe))
      case _ ⇒
        log.debug("Unexpected message on ProcessEventSender when expecting a compiled recipe")
        stopActor()
    }

  def waitForFirstEvent(recipe: CompiledRecipe): Receive =
    handleRejections orElse {
      case firstEvent: TransitionFired ⇒
        notifyReceive(recipe)
        context.become(streaming(firstEvent.newJobsIds - firstEvent.jobId, List(firstEvent)))
      case ReceiveTimeout ⇒
        log.debug("Timeout on ProcessEventSender")
        stopActor()
      case _ ⇒
        log.debug("Unexpected message on ProcessEventSender when expecting the first transition fired event")
        stopActor()
    }

  def streaming(runningJobs: Set[Long], cache: List[Any]): Receive = {
    if(runningJobs.isEmpty) notifyComplete(cache)
    {
      case event: TransitionFired ⇒
        context.become(streaming(runningJobs ++ event.newJobsIds - event.jobId, cache :+ event))
      case event:TransitionFailed if event.strategy.isRetry && waitForRetries ⇒
        context.become(streaming(runningJobs, cache :+ event))
      case event: TransitionFailed ⇒
        context.become(streaming(runningJobs - event.jobId, cache :+ event))
    }
  }
}

