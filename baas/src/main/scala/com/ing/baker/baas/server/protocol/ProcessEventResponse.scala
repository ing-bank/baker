package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.SensoryEventStatus
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.runtime.core
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class ProcessEventResponse(status: SensoryEventStatus) extends BaasResponse

object ProcessEventResponse {

  implicit def protoMap: ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] =
    new ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.ProcessEventResponse] =
        protobuf.ProcessEventResponse

      override def toProto(a: ProcessEventResponse): protobuf.ProcessEventResponse =
        protobuf.ProcessEventResponse(Some(toSensoryEventStatusProto(a.status)))

      override def fromProto(message: protobuf.ProcessEventResponse): Try[ProcessEventResponse] =
        for {
          status <- versioned(message.sensoryEventStatus, "sensoryEventStatus")
        } yield ProcessEventResponse(fromSensoryEventStatusProto(status))
    }

  private def toSensoryEventStatusProto(sensoryEventStatus: core.SensoryEventStatus): protobuf.SensoryEventStatus = {
    sensoryEventStatus match {
      case core.SensoryEventStatus.Received => protobuf.SensoryEventStatus.Received
      case core.SensoryEventStatus.AlreadyReceived => protobuf.SensoryEventStatus.AlreadyReceived
      case core.SensoryEventStatus.Completed => protobuf.SensoryEventStatus.Completed
      case core.SensoryEventStatus.FiringLimitMet => protobuf.SensoryEventStatus.FiringLimitMet
      case core.SensoryEventStatus.ProcessDeleted => protobuf.SensoryEventStatus.ProcessDeleted
      case core.SensoryEventStatus.ReceivePeriodExpired => protobuf.SensoryEventStatus.ReceivePeriodExpired
    }
  }

  private def fromSensoryEventStatusProto(sensoryEventStatus: protobuf.SensoryEventStatus): core.SensoryEventStatus = {
    sensoryEventStatus match {
      case protobuf.SensoryEventStatus.Received => core.SensoryEventStatus.Received
      case protobuf.SensoryEventStatus.AlreadyReceived => core.SensoryEventStatus.AlreadyReceived
      case protobuf.SensoryEventStatus.Completed => core.SensoryEventStatus.Completed
      case protobuf.SensoryEventStatus.FiringLimitMet => core.SensoryEventStatus.FiringLimitMet
      case protobuf.SensoryEventStatus.ProcessDeleted => core.SensoryEventStatus.ProcessDeleted
      case protobuf.SensoryEventStatus.ReceivePeriodExpired => core.SensoryEventStatus.ReceivePeriodExpired
      case _ =>  throw new IllegalArgumentException("Invalid SensoryEventStatus received during deserialisation")
    }
  }
}
