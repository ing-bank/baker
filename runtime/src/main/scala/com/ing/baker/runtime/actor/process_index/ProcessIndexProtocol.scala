package com.ing.baker.runtime.actor.process_index

import com.ing.baker.runtime.actor.InternalBakerMessage
import com.ing.baker.runtime.core.RuntimeEvent

object ProcessIndexProtocol {
  sealed trait ProcessIndexMessage extends InternalBakerMessage {
    val processId: String
  }

  case class CreateProcess(recipeId: String, override val processId: String) extends ProcessIndexMessage

  case class ProcessEvent(override val processId: String, event: RuntimeEvent, correlationId: Option[String]) extends ProcessIndexMessage

  case class GetProcessState(override val processId: String) extends ProcessIndexMessage

  case class GetCompiledRecipe(override val processId: String) extends ProcessIndexMessage

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
  case class ProcessUninitialized(override val processId: String) extends ProcessIndexMessage

  /**
    * A response send in case when a process was already created in the past
    *
    * @param processId The identifier of the processId
    */
  case class ProcessAlreadyInitialized(override val processId: String) extends ProcessIndexMessage

}
