package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.actor.serialization.ProtoMap
import com.ing.baker.runtime.actor.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class VisualStateResponse(visualState: String) extends BaasResponse

object VisualStateResponse {

  implicit def protoMap: ProtoMap[VisualStateResponse, protobuf.VisualStateResponse] =
    new ProtoMap[VisualStateResponse, protobuf.VisualStateResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.VisualStateResponse] =
        protobuf.VisualStateResponse

      override def toProto(a: VisualStateResponse): protobuf.VisualStateResponse =
        protobuf.VisualStateResponse(Some(a.visualState))

      override def fromProto(message: protobuf.VisualStateResponse): Try[VisualStateResponse] =
        for {
          visualState <- versioned(message.visualStateResponse, "visualStateResponse")
        } yield VisualStateResponse(visualState)
    }
}
