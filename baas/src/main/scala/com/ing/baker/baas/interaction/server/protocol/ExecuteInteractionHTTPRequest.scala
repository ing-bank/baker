package com.ing.baker.baas.interaction.server.protocol

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._

import com.ing.baker.baas.server.protocol.BaasRequest
import com.ing.baker.types.Value

import com.ing.baker.runtime.core.actor.serialization.ProtoMap
import com.ing.baker.runtime.core.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class ExecuteInteractionHTTPRequest(input: Seq[Value]) extends BaasRequest

object ExecuteInteractionHTTPRequest {

  implicit def protoMap: ProtoMap[ExecuteInteractionHTTPRequest, protobuf.ExecuteInteractionHTTPRequest] =
    new ProtoMap[ExecuteInteractionHTTPRequest, protobuf.ExecuteInteractionHTTPRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.ExecuteInteractionHTTPRequest] =
        protobuf.ExecuteInteractionHTTPRequest

      override def toProto(a: ExecuteInteractionHTTPRequest): protobuf.ExecuteInteractionHTTPRequest =
        protobuf.ExecuteInteractionHTTPRequest(a.input.map(ctxToProto(_)))

      override def fromProto(message: protobuf.ExecuteInteractionHTTPRequest): Try[ExecuteInteractionHTTPRequest] =
        for {
          input <- message.values.toList.traverse(ctxFromProto(_))
        } yield ExecuteInteractionHTTPRequest(input)
    }
}
