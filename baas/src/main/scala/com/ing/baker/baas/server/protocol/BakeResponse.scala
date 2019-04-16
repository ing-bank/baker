package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.ProcessState
import com.ing.baker.runtime.actortyped.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class BakeResponse(processState: ProcessState) extends BaasResponse

object BakeResponse {

  implicit def protoMap(implicit provider: SerializersProvider): ProtoMap[BakeResponse, protobuf.BakeResponse] =
    new ProtoMap[BakeResponse, protobuf.BakeResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.BakeResponse] =
        protobuf.BakeResponse

      override def toProto(a: BakeResponse): protobuf.BakeResponse =
        protobuf.BakeResponse(Some(ctxToProto(a.processState)))

      override def fromProto(message: protobuf.BakeResponse): Try[BakeResponse] =
        for {
          processStateProto <- versioned(message.processState, "processState")
          processState <- ctxFromProto(processStateProto)(ProcessState.protoMap)
        } yield BakeResponse(processState)
    }
}
