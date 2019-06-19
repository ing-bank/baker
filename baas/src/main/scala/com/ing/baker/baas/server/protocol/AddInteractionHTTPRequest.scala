package com.ing.baker.baas.server.protocol

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}
import com.ing.baker.types.Type
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class AddInteractionHTTPRequest(name: String, uri: String, inputTypes: Map[String, Type]) extends BaasRequest

object AddInteractionHTTPRequest {

  implicit def protoMap: ProtoMap[AddInteractionHTTPRequest, protobuf.AddInteractionHTTPRequest] =
    new ProtoMap[AddInteractionHTTPRequest, protobuf.AddInteractionHTTPRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.AddInteractionHTTPRequest] =
        protobuf.AddInteractionHTTPRequest

      override def toProto(a: AddInteractionHTTPRequest): protobuf.AddInteractionHTTPRequest =
        protobuf.AddInteractionHTTPRequest(Some(a.name), Some(a.uri), a.inputTypes.mapValues(ctxToProto(_)))

      override def fromProto(message: protobuf.AddInteractionHTTPRequest): Try[AddInteractionHTTPRequest] =
        for {
          name <- versioned(message.name, "name")
          uri <- versioned(message.uri, "uri")
          input <- message.input.toList.traverse { case (name0, type0) => ctxFromProto(type0).map(name0 -> _) }
        } yield AddInteractionHTTPRequest(name, uri, input.toMap)
    }
}
