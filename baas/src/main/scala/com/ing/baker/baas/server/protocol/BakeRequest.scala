package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class BakeRequest(recipeId: String) extends BaasRequest

object BakeRequest {

  implicit def protoMap: ProtoMap[BakeRequest, protobuf.BakeRequest] =
    new ProtoMap[BakeRequest, protobuf.BakeRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.BakeRequest] =
        protobuf.BakeRequest

      override def toProto(a: BakeRequest): protobuf.BakeRequest =
        protobuf.BakeRequest(Some(a.recipeId))

      override def fromProto(message: protobuf.BakeRequest): Try[BakeRequest] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield BakeRequest(recipeId)
    }
}
