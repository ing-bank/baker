package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.{common, akka}
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

  private def toSensoryEventStatusProto(sensoryEventStatus: SensoryEventStatus): protobuf.SensoryEventStatus = {
    sensoryEventStatus match {
      case common.SensoryEventStatus.Received => protobuf.SensoryEventStatus.Received
      case common.SensoryEventStatus.AlreadyReceived => protobuf.SensoryEventStatus.AlreadyReceived
      case common.SensoryEventStatus.Completed => protobuf.SensoryEventStatus.Completed
      case common.SensoryEventStatus.FiringLimitMet => protobuf.SensoryEventStatus.FiringLimitMet
      case common.SensoryEventStatus.ProcessDeleted => protobuf.SensoryEventStatus.ProcessDeleted
      case common.SensoryEventStatus.ReceivePeriodExpired => protobuf.SensoryEventStatus.ReceivePeriodExpired
    }
  }

  private def fromSensoryEventStatusProto(sensoryEventStatus: protobuf.SensoryEventStatus): SensoryEventStatus = {
    sensoryEventStatus match {
      case protobuf.SensoryEventStatus.Received => common.SensoryEventStatus.Received
      case protobuf.SensoryEventStatus.AlreadyReceived => common.SensoryEventStatus.AlreadyReceived
      case protobuf.SensoryEventStatus.Completed => common.SensoryEventStatus.Completed
      case protobuf.SensoryEventStatus.FiringLimitMet => common.SensoryEventStatus.FiringLimitMet
      case protobuf.SensoryEventStatus.ProcessDeleted => common.SensoryEventStatus.ProcessDeleted
      case protobuf.SensoryEventStatus.ReceivePeriodExpired => common.SensoryEventStatus.ReceivePeriodExpired
      case _ =>  throw new IllegalArgumentException("Invalid SensoryEventStatus received during deserialisation")
    }
  }
}
