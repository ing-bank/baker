package com.ing.baker.runtime.akka.actor.interaction_manager

import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.javadsl.EventInstance

object InteractionManagerProtocol {

  sealed trait InteractionManagerMessage extends BakerSerializable

  case class ExecuteTransition() extends InteractionManagerMessage

  sealed trait ExecuteTransitionResponse extends InteractionManagerMessage

  case class ExecuteTransitionSuccessful(result: Option[EventInstance])

  /**
    * Technical failure of the interaction
    */
  case class InstanceExecutionFailed() extends ExecuteTransitionResponse

  /**
    * Invalid request, bad ingredients given
    */
  case class InstanceExecutedInvalid() extends ExecuteTransitionResponse
}
