package com.ing.baker.runtime.core.actor.process_index

import akka.actor.ActorRef
import akka.stream.SourceRef
import com.ing.baker.runtime.core.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.core.actor.serialization.BakerSerializable
import com.ing.baker.runtime.core.RuntimeEvent

import scala.concurrent.duration.FiniteDuration

object ProcessIndexProtocol {
  sealed trait ProcessIndexMessage extends BakerSerializable {
    val processId: String
  }

  // -- COMMANDS

  case object GetIndex extends BakerSerializable

  case class Index(entries: Seq[ActorMetadata]) extends BakerSerializable

  case class CreateProcess(recipeId: String, override val processId: String) extends ProcessIndexMessage

  case class ProcessEvent(override val processId: String, event: RuntimeEvent, correlationId: Option[String], waitForRetries: Boolean, timeout: FiniteDuration, receiver: ActorRef) extends ProcessIndexMessage

  case class ProcessEventResponse(override val processId: String) extends ProcessIndexMessage

  case class GetProcessState(override val processId: String) extends ProcessIndexMessage

  case class GetCompiledRecipe(override val processId: String) extends ProcessIndexMessage

  case class RetryBlockedInteraction(override val processId: String, interactionName: String) extends ProcessIndexMessage

  case class ResolveBlockedInteraction(override val processId: String, interactionName: String, output: RuntimeEvent) extends ProcessIndexMessage

  case class StopRetryingInteraction(override val processId: String, interactionName: String) extends ProcessIndexMessage

  // --- RESPONSES

  /**
    * Indicates that a process can no longer receive events because the configured period has expired.
    */
  case class ReceivePeriodExpired(override val processId: String) extends ProcessIndexMessage

  /**
    * @param msg error message for the request
    */
  case class InvalidEvent(override val processId: String, msg: String) extends ProcessIndexMessage

  /**
    * Returned if a process has been deleted
    */
  case class ProcessDeleted(override val processId: String) extends ProcessIndexMessage

  /**
    * Returned if the process is unitialized
    */
  case class NoSuchProcess(override val processId: String) extends ProcessIndexMessage

  /**
    * A response send in case when a process was already created in the past
    *
    * @param processId The identifier of the processId
    */
  case class ProcessAlreadyExists(override val processId: String) extends ProcessIndexMessage

}
