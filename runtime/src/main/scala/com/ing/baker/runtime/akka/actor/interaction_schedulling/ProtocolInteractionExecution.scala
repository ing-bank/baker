package com.ing.baker.runtime.akka.actor.interaction_schedulling

import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}

/**
  * Protocol executed after a match between a QuestMandate and InteractionAgent has been made and after both
  * have committed.
  *
  * A simple request from the manager to the agent for execution with specific ingredients is done using the
  * ExecuteInstance message, the outcome comes in the form of either the response messages InstanceExecutedSuccessfully,
  * InstanceExecutionFailed or InvalidExecution
  *
  */
sealed trait ProtocolInteractionExecution extends BakerSerializable

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
  case class InstanceExecutionFailed() extends ProtocolInteractionExecution

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
