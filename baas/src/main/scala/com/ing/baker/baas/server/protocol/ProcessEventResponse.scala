package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.versioned
import com.ing.baker.runtime.akka.actor.serialization.protomappings.SensoryEventStatusMappingHelper
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.runtime.common.SensoryEventStatus
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class ProcessEventResponse(status: SensoryEventStatus) extends BaasResponse

object ProcessEventResponse {

  implicit def protoMap: ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] =
    new ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.ProcessEventResponse] =
        protobuf.ProcessEventResponse

      override def toProto(a: ProcessEventResponse): protobuf.ProcessEventResponse =
        protobuf.ProcessEventResponse(Some(SensoryEventStatusMappingHelper.toProto(a.status)))

      override def fromProto(message: protobuf.ProcessEventResponse): Try[ProcessEventResponse] =
        for {
          status <- versioned(message.sensoryEventStatus, "sensoryEventStatus")
        } yield ProcessEventResponse(SensoryEventStatusMappingHelper.fromProto(status).get)
    }
}
