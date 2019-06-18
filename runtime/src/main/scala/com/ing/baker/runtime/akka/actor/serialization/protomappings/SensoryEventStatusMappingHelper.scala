package com.ing.baker.runtime.akka.actor.serialization.protomappings

import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.common.SensoryEventStatus

import scala.util.{Failure, Success, Try}

object SensoryEventStatusMappingHelper {

  def toProto(status: SensoryEventStatus): protobuf.SensoryEventStatus = {
    status match {
      case SensoryEventStatus.Received => protobuf.SensoryEventStatus.RECEIVED
      case SensoryEventStatus.Completed => protobuf.SensoryEventStatus.COMPLETED
      case SensoryEventStatus.FiringLimitMet => protobuf.SensoryEventStatus.FIRING_LIMIT_MET
      case SensoryEventStatus.ReceivePeriodExpired => protobuf.SensoryEventStatus.RECEIVE_PERIOD_EXPIRED
      case SensoryEventStatus.AlreadyReceived => protobuf.SensoryEventStatus.ALREADY_RECEIVED
      case SensoryEventStatus.ProcessDeleted => protobuf.SensoryEventStatus.PROCESS_DELETED
    }
  }

  def fromProto(protoStatus: protobuf.SensoryEventStatus): Try[SensoryEventStatus] = {
    protoStatus match {
      case protobuf.SensoryEventStatus.RECEIVED => Success(SensoryEventStatus.Received)
      case protobuf.SensoryEventStatus.COMPLETED => Success(SensoryEventStatus.Completed)
      case protobuf.SensoryEventStatus.FIRING_LIMIT_MET => Success(SensoryEventStatus.FiringLimitMet)
      case protobuf.SensoryEventStatus.RECEIVE_PERIOD_EXPIRED => Success(SensoryEventStatus.ReceivePeriodExpired)
      case protobuf.SensoryEventStatus.ALREADY_RECEIVED => Success(SensoryEventStatus.AlreadyReceived)
      case protobuf.SensoryEventStatus.PROCESS_DELETED => Success(SensoryEventStatus.ProcessDeleted)
      case protobuf.SensoryEventStatus.Unrecognized(value) => Failure(new IllegalStateException(s"Received illegal value '$value' for enumeration SensoryEventStatus"))
    }
  }

}
