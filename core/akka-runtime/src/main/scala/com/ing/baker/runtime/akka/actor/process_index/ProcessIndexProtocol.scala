package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.ActorRef
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexActor.ActorMetadata
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.scaladsl.{EventInstance, SensoryEventResult}
import com.ing.baker.runtime.common.{RejectReason, SensoryEventStatus}

import scala.concurrent.duration.FiniteDuration

object ProcessIndexProtocol {

  sealed trait ProcessIndexMessage extends BakerSerializable {
    val recipeInstanceId: String
  }

  case object GetIndex extends BakerSerializable

  case class Index(entries: Seq[ActorMetadata]) extends BakerSerializable

  case class ProcessEventResponse(recipeInstanceId: String) extends ProcessIndexMessage

  case class GetProcessState(recipeInstanceId: String) extends ProcessIndexMessage

  case class GetCompiledRecipe(recipeInstanceId: String) extends ProcessIndexMessage

  case class RetryBlockedInteraction(recipeInstanceId: String, interactionName: String) extends ProcessIndexMessage

  case class StopRetryingInteraction(recipeInstanceId: String, interactionName: String) extends ProcessIndexMessage

  case class ResolveBlockedInteraction(recipeInstanceId: String, interactionName: String, output: EventInstance) extends ProcessIndexMessage

  /**
    * Failure when attempting to resolve a blocked interaction, the event is not of valid type according with the recipe
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    * @param msg error message for the request
    */
  case class InvalidEventWhenResolveBlocked(recipeInstanceId: String, msg: String) extends ProcessIndexMessage

  /**
    * Returned if a process has been deleted
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class ProcessDeleted(recipeInstanceId: String) extends ProcessIndexMessage

  /**
    * Returned if the process does not exist
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class NoSuchProcess(recipeInstanceId: String) extends ProcessIndexMessage

  /**
    * Command requesting the creation of a new process with chosen recipe and predefined identifier
    *
    * @param recipeId Id of the recipe to use, must exist on the Recipe Manager
    * @param recipeInstanceId To be used for the process, must not be previously used
    */
  case class CreateProcess(recipeId: String, recipeInstanceId: String) extends ProcessIndexMessage

  /**
    * Returned if there was already another process using the predefined process id
    *
    * @param recipeInstanceId Process id meant to be used but already was occupied
    */
  case class ProcessAlreadyExists(recipeInstanceId: String) extends ProcessIndexMessage

  /**
    * Command requesting the firing of a sensory event on corresponding process instance.
    *
    * @param recipeInstanceId The identifier of the process instance
    * @param event Sensory event to be fired
    * @param correlationId Correlation token used for ... TODO come up with a good description of correlations
    * @param timeout Waiting time for an instance to produce some response to this request
    * @param reaction Expected reaction from the ProcessEventSender actor, see SensoryEventReaction
    */
  case class ProcessEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String], timeout: FiniteDuration, reaction: FireSensoryEventReaction) extends ProcessIndexMessage

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

    /**
      * The process instance should notify when an specific event has occurred on consequence of the initial fired event
      *
      * @param waitForRetries Expect retires of failed transitions
      * @param onEvent event to be waited for
      */
    case class NotifyOnEvent(waitForRetries: Boolean, onEvent: String) extends FireSensoryEventReaction
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
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class ReceivePeriodExpired(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ReceivePeriodExpired
    }

    /**
      * @param msg error message for the request
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class InvalidEvent(recipeInstanceId: String, msg: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.InvalidEvent
    }

    /**
      * Returned if a process has been deleted
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class RecipeInstanceDeleted(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ProcessDeleted
    }

    /**
      * Returned if the process is uninitialized
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class NoSuchRecipeInstance(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.NoSuchProcess
    }

    /**
      * The firing limit, the number of times this event may fire, was met.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class FiringLimitMet(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.FiringLimitMet
    }

    /**
      * An event with the same correlation id was already received.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      * @param correlationId The identifier used to secure uniqueness
      */
    case class AlreadyReceived(recipeInstanceId: String, correlationId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.AlreadyReceived
    }
  }
}
