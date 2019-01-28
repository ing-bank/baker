package com.ing.baker.runtime.core

import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol

sealed trait BakerResponseEventProtocol {

  def toSensoryEventStatus: SensoryEventStatus = this match {
    case BakerResponseEventProtocol.InstanceTransitionFired => SensoryEventStatus.Received
    case BakerResponseEventProtocol.InstanceTransitionNotEnabled => SensoryEventStatus.FiringLimitMet
    case BakerResponseEventProtocol.InstanceAlreadyReceived => SensoryEventStatus.AlreadyReceived
    case BakerResponseEventProtocol.IndexNoSuchProcess(processId) => throw new NoSuchProcessException(s"No such process: $processId")
    case BakerResponseEventProtocol.IndexReceivePeriodExpired => SensoryEventStatus.ReceivePeriodExpired
    case BakerResponseEventProtocol.IndexProcessDeleted => SensoryEventStatus.ProcessDeleted
    case BakerResponseEventProtocol.IndexInvalidEvent(invalidEventMessage) => throw new IllegalArgumentException(invalidEventMessage)
  }
}

object BakerResponseEventProtocol {

  case object InstanceTransitionFired extends BakerResponseEventProtocol

  case object InstanceTransitionNotEnabled extends BakerResponseEventProtocol

  case object InstanceAlreadyReceived extends BakerResponseEventProtocol

  case class IndexNoSuchProcess(processId: String) extends BakerResponseEventProtocol

  case object IndexReceivePeriodExpired extends BakerResponseEventProtocol

  case object IndexProcessDeleted extends BakerResponseEventProtocol

  case class IndexInvalidEvent(message: String) extends BakerResponseEventProtocol

  def fromProtocols(msg: Any): BakerResponseEventProtocol = msg match {
    case _: ProcessInstanceProtocol.TransitionFired => InstanceTransitionFired
    case _: ProcessInstanceProtocol.TransitionNotEnabled => InstanceTransitionNotEnabled
    case _: ProcessInstanceProtocol.AlreadyReceived => InstanceAlreadyReceived
    case ProcessIndexProtocol.NoSuchProcess(processId) => IndexNoSuchProcess(processId)
    case ProcessIndexProtocol.ReceivePeriodExpired(_) => IndexReceivePeriodExpired
    case ProcessIndexProtocol.ProcessDeleted(_) => IndexProcessDeleted
    case ProcessIndexProtocol.InvalidEvent(_, invalidEventMessage) => IndexInvalidEvent(invalidEventMessage)
    case msg@_ => throw new BakerException(s"Unexpected actor response message: $msg")
  }

}
