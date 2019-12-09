package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{ Actor, ActorLogging, ActorRef, Props, ReceiveTimeout }
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{ EventInstance, EventReceived, EventRejected, SensoryEventResult }
import com.ing.baker.types.{ PrimitiveValue, Value }

object SensoryEventResponseHandler {

  def apply(receiver: ActorRef, command: ProcessEvent, ingredientsFilter: Seq[String] = Seq.empty): Props =
    Props(new SensoryEventResponseHandler(receiver, command, ingredientsFilter))
}

/**
 * An actor which builds the response to fireSensoryEvent* requests
 * - Obtains the data from the process instance (by accumulating transition firing outcomes)
 * - Publishes events to the system event stream
 * - Does involving logging
 */
class SensoryEventResponseHandler(receiver: ActorRef, command: ProcessEvent, ingredientsFilter: Seq[String])
  extends Actor with ActorLogging {

  context.setReceiveTimeout(command.timeout)

  val waitForRetries: Boolean = command.reaction match {
    case FireSensoryEventReaction.NotifyWhenReceived => false
    case FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries0) => waitForRetries0
    case FireSensoryEventReaction.NotifyBoth(waitForRetries0, _) => waitForRetries0
    case FireSensoryEventReaction.NotifyOnEvent(waitForRetries0, _) => waitForRetries0
  }

  def notifyReceive(recipe: CompiledRecipe): Unit = {
    context.system.eventStream.publish(
      EventReceived(
        System.currentTimeMillis(),
        recipe.name,
        recipe.recipeId,
        command.recipeInstanceId,
        command.correlationId,
        command.event))
    command.reaction match {
      case FireSensoryEventReaction.NotifyWhenCompleted(_) =>
        ()
      case FireSensoryEventReaction.NotifyOnEvent(_, _) =>
        ()
      case FireSensoryEventReaction.NotifyWhenReceived =>
        receiver ! ProcessEventReceivedResponse(SensoryEventStatus.Received)
      case FireSensoryEventReaction.NotifyBoth(_, _) =>
        receiver ! ProcessEventReceivedResponse(SensoryEventStatus.Received)
    }
  }

  def notifyComplete(cache: List[Any]): Unit = {
    def runtimeEvents: List[EventInstance] = cache.flatMap {
      case fired: TransitionFired => Option(fired.output.asInstanceOf[EventInstance])
      case _ => None
    }

    def result = SensoryEventResult(
      sensoryEventStatus = SensoryEventStatus.Completed,
      eventNames = runtimeEvents.map(_.name),
      ingredients = filterIngredientValues(runtimeEvents.flatMap(_.providedIngredients).toMap)
    )

    command.reaction match {
      case FireSensoryEventReaction.NotifyBoth(_, alternativeReceiver) =>
        alternativeReceiver ! ProcessEventCompletedResponse(result)
      case _ =>
        receiver ! ProcessEventCompletedResponse(result)
    }
    stopActor()
  }

  private def filterIngredientValues(ingredients: Map[String, Value]): Map[String, Value] =
    ingredients.map(ingredient =>
      if (ingredientsFilter.contains(ingredient._1))
        ingredient._1 -> PrimitiveValue("")
      else
        ingredient)

  def rejectWith(rejection: FireSensoryEventRejection): Unit = {
    log.debug("Stopping SensoryEventResponseHandler and rejecting request")
    log.debug("Reject reason: " + rejection.asReason)
    log.debug("message: " + rejection)
    context.system.eventStream.publish(
      EventRejected(
        System.currentTimeMillis(),
        command.recipeInstanceId,
        command.correlationId,
        command.event,
        rejection.asReason))
    command.reaction match {
      case FireSensoryEventReaction.NotifyBoth(_, completeReceiver) =>
        receiver ! rejection; completeReceiver ! rejection
      case FireSensoryEventReaction.NotifyOnEvent(_, _) =>
        receiver ! rejection
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
    command.reaction match {
      case FireSensoryEventReaction.NotifyOnEvent(_, onEvent)
        if Option(cache.head.asInstanceOf[TransitionFired].output.asInstanceOf[EventInstance]).exists(_.name == onEvent) =>
        notifyComplete(cache.reverse)
        PartialFunction {_ => ()}

      case FireSensoryEventReaction.NotifyWhenCompleted(_) if runningJobs.isEmpty =>
        notifyComplete(cache.reverse)
        PartialFunction {_ => ()}

      case FireSensoryEventReaction.NotifyBoth(_, _) if runningJobs.isEmpty =>
        notifyComplete(cache.reverse)
        PartialFunction {_ => ()}

      case _ =>
        PartialFunction {
          case event: TransitionFired ⇒
            context.become(streaming(runningJobs ++ event.newJobsIds - event.jobId, event :: cache))
          case event: TransitionFailed if event.strategy.isRetry && waitForRetries ⇒
            context.become(streaming(runningJobs, event :: cache))
          case event: TransitionFailed ⇒
            context.become(streaming(runningJobs - event.jobId, event :: cache))
          case ReceiveTimeout ⇒
            log.debug("Timeout on SensoryEventResponseHandler when streaming")
            stopActor()
          case message ⇒
            log.debug(s"Unexpected message $message on SensoryEventResponseHandler when streaming")
            stopActor()
        }
    }
  }
}
