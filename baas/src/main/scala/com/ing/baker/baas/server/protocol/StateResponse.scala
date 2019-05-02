package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.ProcessState

import com.ing.baker.runtime.actor.serialization.ProtoMap
import com.ing.baker.runtime.actor.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class StateResponse(processState: ProcessState) extends BaasResponse

object StateResponse {

  implicit def protoMap: ProtoMap[StateResponse, protobuf.StateResponse] =
    new ProtoMap[StateResponse, protobuf.StateResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.StateResponse] =
        protobuf.StateResponse

      override def toProto(a: StateResponse): protobuf.StateResponse =
        protobuf.StateResponse(Some(ctxToProto(a.processState)))

      override def fromProto(message: protobuf.StateResponse): Try[StateResponse] =
        for {
          processStateProto <- versioned(message.processState, "processState")
          processState <- ctxFromProto(processStateProto)(ProcessState.protoMap)
        } yield StateResponse(processState)
    }
}
