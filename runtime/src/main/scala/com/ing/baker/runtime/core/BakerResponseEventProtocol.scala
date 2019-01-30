package com.ing.baker.runtime.core

import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol

sealed trait BakerResponseEventProtocol {

  def toSensoryEventStatus: SensoryEventStatus = this match {
    case BakerResponseEventProtocol.InstanceTransitionFired(_) =>
      SensoryEventStatus.Received

    case BakerResponseEventProtocol.InstanceTransitionNotEnabled(_) =>
      SensoryEventStatus.FiringLimitMet

    case BakerResponseEventProtocol.InstanceAlreadyReceived(_) =>
      SensoryEventStatus.AlreadyReceived

    case BakerResponseEventProtocol.IndexNoSuchProcess(event) =>
      throw new NoSuchProcessException(s"No such process: ${event.asInstanceOf[ProcessIndexProtocol.NoSuchProcess].processId}")

    case BakerResponseEventProtocol.IndexReceivePeriodExpired(_) =>
      SensoryEventStatus.ReceivePeriodExpired

    case BakerResponseEventProtocol.IndexProcessDeleted(_) =>
      SensoryEventStatus.ProcessDeleted

    case BakerResponseEventProtocol.IndexInvalidEvent(event) =>
      throw new IllegalArgumentException(event.asInstanceOf[ProcessIndexProtocol.InvalidEvent].msg)
  }

}

object BakerResponseEventProtocol {

  case class InstanceTransitionFired(value: Any) extends BakerResponseEventProtocol

  case class InstanceTransitionNotEnabled(value: Any) extends BakerResponseEventProtocol

  case class InstanceAlreadyReceived(value: Any) extends BakerResponseEventProtocol

  case class IndexNoSuchProcess(value: Any) extends BakerResponseEventProtocol

  case class IndexReceivePeriodExpired(value: Any) extends BakerResponseEventProtocol

  case class IndexProcessDeleted(value: Any) extends BakerResponseEventProtocol

  case class IndexInvalidEvent(value: Any) extends BakerResponseEventProtocol

  def fromProtocols(msg: Any): BakerResponseEventProtocol = msg match {
    case event: ProcessInstanceProtocol.TransitionFired => InstanceTransitionFired(event)
    case event: ProcessInstanceProtocol.TransitionNotEnabled => InstanceTransitionNotEnabled(event)
    case event: ProcessInstanceProtocol.AlreadyReceived => InstanceAlreadyReceived(event)
    case event: ProcessIndexProtocol.NoSuchProcess => IndexNoSuchProcess(event)
    case event: ProcessIndexProtocol.ReceivePeriodExpired => IndexReceivePeriodExpired(event)
    case event: ProcessIndexProtocol.ProcessDeleted => IndexProcessDeleted(event)
    case event: ProcessIndexProtocol.InvalidEvent => IndexInvalidEvent(event)
    case msg@_ => throw new BakerException(s"Unexpected actor response message: $msg")
  }

}
