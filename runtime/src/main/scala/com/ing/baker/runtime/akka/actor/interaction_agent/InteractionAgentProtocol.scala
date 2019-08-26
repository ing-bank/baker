package com.ing.baker.runtime.akka.actor.interaction_agent

import akka.remote.ContainerFormats.ActorRef
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}

object InteractionAgentProtocol {

  sealed trait InteractionAgentMessage extends BakerSerializable

  case class Register(interactionAgentDescriptor: InteractionAgentDescriptor,
                      agentRef: ActorRef) extends InteractionAgentMessage

  case class ExecuteInstance(input: Seq[IngredientInstance])

  sealed trait ExecuteInstanceResponse extends InteractionAgentMessage

  /**
    * Instance executed successfully
    * @param result the EventInstance that is created, empty if interaction does not return an Event
    */
  case class InstanceExecutedSuccessfully(result: Option[EventInstance]) extends ExecuteInstanceResponse

  /**
    * Technical failure of the interaction
    */
  case class InstanceExecutionFailed() extends ExecuteInstanceResponse

  /**
    * Invalid request, bad ingredients given
    */
  case class InstanceExecutedInvalid() extends ExecuteInstanceResponse
}
