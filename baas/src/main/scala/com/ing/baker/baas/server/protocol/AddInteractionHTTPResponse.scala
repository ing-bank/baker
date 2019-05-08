package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.actor.serialization.ProtoMap
import com.ing.baker.runtime.core.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class AddInteractionHTTPResponse(description: String) extends BaasResponse

object AddInteractionHTTPResponse {

  implicit def protoMap: ProtoMap[AddInteractionHTTPResponse, protobuf.AddInteractionHTTPResponse] =
    new ProtoMap[AddInteractionHTTPResponse, protobuf.AddInteractionHTTPResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.AddInteractionHTTPResponse] =
        protobuf.AddInteractionHTTPResponse

      override def toProto(a: AddInteractionHTTPResponse): protobuf.AddInteractionHTTPResponse =
        protobuf.AddInteractionHTTPResponse(Some(a.description))

      override def fromProto(message: protobuf.AddInteractionHTTPResponse): Try[AddInteractionHTTPResponse] =
        for {
          description <- versioned(message.message, "message")
        } yield AddInteractionHTTPResponse(description)
    }
}
