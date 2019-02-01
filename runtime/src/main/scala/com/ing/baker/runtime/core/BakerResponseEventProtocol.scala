package com.ing.baker.runtime.core

import com.ing.baker.runtime.actor.process_index.{ProcessIndexProtocol => idxProtocol}
import com.ing.baker.runtime.actor.process_instance.{ProcessInstanceProtocol => insProtocol}

sealed trait BakerResponseEventProtocol {

  def toSensoryEventStatus: SensoryEventStatus = this match {
    case BakerResponseEventProtocol.InstanceTransitionFired(_) =>
      SensoryEventStatus.Received

    case BakerResponseEventProtocol.InstanceTransitionNotEnabled(_) =>
      SensoryEventStatus.FiringLimitMet

    case BakerResponseEventProtocol.InstanceAlreadyReceived(_) =>
      SensoryEventStatus.AlreadyReceived

    case BakerResponseEventProtocol.IndexNoSuchProcess(event) =>
      throw new NoSuchProcessException(s"No such process: ${event.asInstanceOf[idxProtocol.NoSuchProcess].processId}")

    case BakerResponseEventProtocol.IndexReceivePeriodExpired(_) =>
      SensoryEventStatus.ReceivePeriodExpired

    case BakerResponseEventProtocol.IndexProcessDeleted(_) =>
      SensoryEventStatus.ProcessDeleted

    case BakerResponseEventProtocol.IndexInvalidEvent(event) =>
      throw new IllegalArgumentException(event.asInstanceOf[idxProtocol.InvalidEvent].msg)
  }

}

object BakerResponseEventProtocol {

  case class InstanceTransitionFired(value: insProtocol.TransitionFired) extends BakerResponseEventProtocol

  case class InstanceTransitionNotEnabled(value: insProtocol.TransitionNotEnabled) extends BakerResponseEventProtocol

  case class InstanceAlreadyReceived(value: insProtocol.AlreadyReceived) extends BakerResponseEventProtocol

  case class IndexNoSuchProcess(value: idxProtocol.NoSuchProcess) extends BakerResponseEventProtocol

  case class IndexReceivePeriodExpired(value: idxProtocol.ReceivePeriodExpired) extends BakerResponseEventProtocol

  case class IndexProcessDeleted(value: idxProtocol.ProcessDeleted) extends BakerResponseEventProtocol

  case class IndexInvalidEvent(value: idxProtocol.InvalidEvent) extends BakerResponseEventProtocol

  def fromProtocols(msg: Any): BakerResponseEventProtocol = msg match {
    case event: insProtocol.TransitionFired => InstanceTransitionFired(event)
    case event: insProtocol.TransitionNotEnabled => InstanceTransitionNotEnabled(event)
    case event: insProtocol.AlreadyReceived => InstanceAlreadyReceived(event)
    case event: idxProtocol.NoSuchProcess => IndexNoSuchProcess(event)
    case event: idxProtocol.ReceivePeriodExpired => IndexReceivePeriodExpired(event)
    case event: idxProtocol.ProcessDeleted => IndexProcessDeleted(event)
    case event: idxProtocol.InvalidEvent => IndexInvalidEvent(event)
    case msg@_ => throw new BakerException(s"Unexpected actor response message: $msg")
  }

}
