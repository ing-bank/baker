package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{Actor, ActorRef, Props, ReceiveTimeout}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.RuntimeEvent
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{FireSensoryEventReaction, FireSensoryEventRejection, ProcessEvent}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.events.{EventReceived, EventRejected}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.SensoryEventResult
import org.slf4j.{Logger, LoggerFactory}

object SensoryEventResponseHandler {

  def apply(receiver: ActorRef, command: ProcessEvent): Props =
    Props(new SensoryEventResponseHandler(receiver, command))
}

/**
  * An actor which builds the response to fireSensoryEvent* requests
  * - Obtains the data from the process instance (by accumulating transition firing outcomes)
  * - Publishes events to the system event stream
  * - Does involving logging
  */
class SensoryEventResponseHandler(receiver: ActorRef, command: ProcessEvent) extends Actor {

  context.setReceiveTimeout(command.timeout)

  val log: Logger = LoggerFactory.getLogger(classOf[SensoryEventResponseHandler])

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
    def runtimeEvents: List[RuntimeEvent] = cache.flatMap {
      case fired: TransitionFired => Option(fired.output.asInstanceOf[RuntimeEvent])
      case _ => None
    }
    def result = SensoryEventResult(
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
    log.debug("Stopping SensoryEventResponseHandler and rejecting request")
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
    log.debug("Stopping the SensoryEventResponseHandler")
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
      case ReceiveTimeout ⇒
        log.debug("Timeout on SensoryEventResponseHandler when expecting a compiled recipe")
        stopActor()
      case message ⇒
        log.debug(s"Unexpected message $message on SensoryEventResponseHandler when expecting a compiled recipe")
        stopActor()
    }

  def waitForFirstEvent(recipe: CompiledRecipe): Receive =
    handleRejections orElse {
      case firstEvent: TransitionFired ⇒
        notifyReceive(recipe)
        context.become(streaming(firstEvent.newJobsIds - firstEvent.jobId, List(firstEvent)))
      case ReceiveTimeout ⇒
        log.debug("Timeout on SensoryEventResponseHandler when expecting the first transition fired event")
        stopActor()
      case message ⇒
        log.debug(s"Unexpected message $message on SensoryEventResponseHandler when expecting the first transition fired event")
        stopActor()
    }

  def streaming(runningJobs: Set[Long], cache: List[Any]): Receive = {
    if(runningJobs.isEmpty) notifyComplete(cache)
    PartialFunction {
      case event: TransitionFired ⇒
        context.become(streaming(runningJobs ++ event.newJobsIds - event.jobId, cache :+ event))
      case event: TransitionFailed if event.strategy.isRetry && waitForRetries ⇒
        context.become(streaming(runningJobs, cache :+ event))
      case event: TransitionFailed ⇒
        context.become(streaming(runningJobs - event.jobId, cache :+ event))
      case ReceiveTimeout ⇒
        log.debug("Timeout on SensoryEventResponseHandler when streaming")
        stopActor()
      case message ⇒
        log.debug(s"Unexpected message $message on SensoryEventResponseHandler when streaming")
        stopActor()
    }
  }
}
