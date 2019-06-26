package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.ActorRef
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.scaladsl.{RuntimeEvent, SensoryEventResult}
import com.ing.baker.runtime.common.{RejectReason, SensoryEventStatus}

import scala.concurrent.duration.FiniteDuration

object ProcessIndexProtocol {

  sealed trait ProcessIndexMessage extends BakerSerializable {
    val processId: String
  }

  case object GetIndex extends BakerSerializable

  case class Index(entries: Seq[ActorMetadata]) extends BakerSerializable

  case class ProcessEventResponse(processId: String) extends ProcessIndexMessage

  case class GetProcessState(processId: String) extends ProcessIndexMessage

  case class GetCompiledRecipe(processId: String) extends ProcessIndexMessage

  case class RetryBlockedInteraction(processId: String, interactionName: String) extends ProcessIndexMessage

  case class StopRetryingInteraction(processId: String, interactionName: String) extends ProcessIndexMessage

  case class ResolveBlockedInteraction(processId: String, interactionName: String, output: RuntimeEvent) extends ProcessIndexMessage

  /**
    * Failure when attempting to resolve a blocked interaction, the event is not of valid type according with the recipe
    *
    * @param processId The identifier of the processId
    * @param msg error message for the request
    */
  case class InvalidEventWhenResolveBlocked(processId: String, msg: String) extends ProcessIndexMessage

  /**
    * Returned if a process has been deleted
    *
    * @param processId The identifier of the processId
    */
  case class ProcessDeleted(processId: String) extends ProcessIndexMessage

  /**
    * Returned if the process does not exist
    *
    * @param processId The identifier of the processId
    */
  case class NoSuchProcess(processId: String) extends ProcessIndexMessage

  /**
    * Command requesting the creation of a new process with chosen recipe and predefined identifier
    *
    * @param recipeId Id of the recipe to use, must exist on the Recipe Manager
    * @param processId To be used for the process, must not be previously used
    */
  case class CreateProcess(recipeId: String, processId: String) extends ProcessIndexMessage

  /**
    * Returned if there was already another process using the predefined process id
    *
    * @param processId Process id meant to be used but already was occupied
    */
  case class ProcessAlreadyExists(processId: String) extends ProcessIndexMessage

  /**
    * Command requesting the firing of a sensory event on corresponding process instance.
    *
    * @param processId The identifier of the process instance
    * @param event Sensory event to be fired
    * @param correlationId Correlation token used for ... TODO come up with a good description of correlations
    * @param timeout Waiting time for an instance to produce some response to this request
    * @param reaction Expected reaction from the ProcessEventSender actor, see SensoryEventReaction
    */
  case class ProcessEvent(processId: String, event: RuntimeEvent, correlationId: Option[String], timeout: FiniteDuration, reaction: FireSensoryEventReaction) extends ProcessIndexMessage

  /**
    * Expected reactions when firing a sensory event
    */
  sealed trait FireSensoryEventReaction

  object FireSensoryEventReaction {

    /**
      * The process instance should only notify as soon as it accepts the sensory event, but before the transitions
      * start cascading
      */
    case object NotifyWhenReceived extends FireSensoryEventReaction

    /**
      * The process instance should only notify when all transitions affected by the sensory event finish cascading
      *
      * @param waitForRetries Expect retries of failed transitions
      */
    case class NotifyWhenCompleted(waitForRetries: Boolean) extends FireSensoryEventReaction

    /**
      * The process instance should notify both previous scenarios, an extra actor reference is used for the completion
      * notification
      *
      * @param waitForRetries Expect retires of failed transitions
      * @param completeReceiver Actor to be used to notify completion
      */
    case class NotifyBoth(waitForRetries: Boolean, completeReceiver: ActorRef) extends FireSensoryEventReaction
  }

  case class ProcessEventReceivedResponse(status: SensoryEventStatus) extends BakerSerializable

  case class ProcessEventCompletedResponse(result: SensoryEventResult) extends BakerSerializable

  /**
    * Possible failures when firing a sensory event
    */
  sealed trait FireSensoryEventRejection extends ProcessIndexMessage {

    def asReason: RejectReason
  }

  object FireSensoryEventRejection {

    /**
      * Indicates that a process can no longer receive events because the configured period has expired.
      *
      * @param processId The identifier of the processId
      */
    case class ReceivePeriodExpired(processId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ReceivePeriodExpired
    }

    /**
      * @param msg error message for the request
      * @param processId The identifier of the processId
      */
    case class InvalidEvent(processId: String, msg: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.InvalidEvent
    }

    /**
      * Returned if a process has been deleted
      *
      * @param processId The identifier of the processId
      */
    case class ProcessDeleted(processId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ProcessDeleted
    }

    /**
      * Returned if the process is uninitialized
      *
      * @param processId The identifier of the processId
      */
    case class NoSuchProcess(processId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.NoSuchProcess
    }

    /**
      * The firing limit, the number of times this event may fire, was met.
      *
      * @param processId The identifier of the processId
      */
    case class FiringLimitMet(processId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.FiringLimitMet
    }

    /**
      * An event with the same correlation id was already received.
      *
      * @param processId The identifier of the processId
      * @param correlationId The identifier used to secure uniqueness
      */
    case class AlreadyReceived(processId: String, correlationId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.AlreadyReceived
    }
  }
}
