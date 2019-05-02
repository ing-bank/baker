package com.ing.baker.baas.interaction.server.protocol

import com.ing.baker.runtime.core.RuntimeEvent

import cats.instances.option._
import cats.instances.try_._
import cats.syntax.traverse._

import com.ing.baker.baas.server.protocol.BaasRequest

import com.ing.baker.runtime.actor.serialization.ProtoMap
import com.ing.baker.runtime.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class ExecuteInteractionHTTPResponse(runtimeEventOptional: Option[RuntimeEvent]) extends BaasRequest

object ExecuteInteractionHTTPResponse {

  implicit def protoMap: ProtoMap[ExecuteInteractionHTTPResponse, protobuf.ExecuteInteractionHTTPResponse] =
    new ProtoMap[ExecuteInteractionHTTPResponse, protobuf.ExecuteInteractionHTTPResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.ExecuteInteractionHTTPResponse] =
        protobuf.ExecuteInteractionHTTPResponse

      override def toProto(a: ExecuteInteractionHTTPResponse): protobuf.ExecuteInteractionHTTPResponse =
        protobuf.ExecuteInteractionHTTPResponse(a.runtimeEventOptional.map(ctxToProto(_)))

      override def fromProto(message: protobuf.ExecuteInteractionHTTPResponse): Try[ExecuteInteractionHTTPResponse] =
        for {
          runtimeEventOptional <- message.runtimeEvent.traverse(ctxFromProto(_))
        } yield ExecuteInteractionHTTPResponse(runtimeEventOptional)
    }
}
