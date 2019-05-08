package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class AddRecipeResponse(recipeId: String) extends BaasResponse

object AddRecipeResponse {

  implicit def protoMap: ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] =
    new ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.AddRecipeResponse] =
        protobuf.AddRecipeResponse

      override def toProto(a: AddRecipeResponse): protobuf.AddRecipeResponse =
        protobuf.AddRecipeResponse(Some(a.recipeId))

      override def fromProto(message: protobuf.AddRecipeResponse): Try[AddRecipeResponse] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield AddRecipeResponse(recipeId)
    }
}
