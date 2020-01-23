package com.ing.baker.baas.protocol

import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.types.Type

/**
  * Protocol executed after a match between a QuestMandate and InteractionAgent has been made and after both
  * have committed.
  *
  * A simple request from the manager to the agent for execution with specific ingredients is done using the
  * ExecuteInstance message, the outcome comes in the form of either the response messages InstanceExecutedSuccessfully,
  * InstanceExecutionFailed or InvalidExecution
  *
  */
sealed trait ProtocolInteractionExecution

object ProtocolInteractionExecution {

  case class ExecuteInstance(input: Seq[IngredientInstance]) extends ProtocolInteractionExecution

  /**
    * Instance executed successfully
    * @param result the EventInstance that is created, empty if interaction does not return an Event
    */
  case class InstanceExecutedSuccessfully(result: Option[EventInstance]) extends ProtocolInteractionExecution

  /**
    * Technical failure of the interaction
    */
  case class InstanceExecutionFailed(message: String) extends ProtocolInteractionExecution

  /**
    * Communicates the interaction interface
    */
  case class InstanceInterface(name: String, input: Seq[Type]) extends ProtocolInteractionExecution

  /**
    * Technical failure of the interaction
    */
  case class InstanceExecutionTimedOut() extends ProtocolInteractionExecution

  /**
    * Technical failure of the interaction
    */
  case object NoInstanceFound extends ProtocolInteractionExecution

  /**
    * Invalid request, bad ingredients given
    */
  case class InvalidExecution() extends ProtocolInteractionExecution
}
