package com.ing.baker.runtime.baas

import BaaSProtocol._
import com.ing.baker.runtime.akka.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import scalapb.GeneratedMessageCompanion

import scala.util.Try

object BaaSProto {

  implicit val baaSRemoteFailureProto: ProtoMap[BaaSRemoteFailure, protobuf.BaaSRemoteFailure] =
    new ProtoMap[BaaSRemoteFailure, protobuf.BaaSRemoteFailure] {

      override def companion: GeneratedMessageCompanion[protobuf.BaaSRemoteFailure] =
        protobuf.BaaSRemoteFailure

      override def toProto(a: BaaSRemoteFailure): protobuf.BaaSRemoteFailure =
        protobuf.BaaSRemoteFailure(Some(a.message))

      override def fromProto(message: protobuf.BaaSRemoteFailure): Try[BaaSRemoteFailure] =
        versioned(message.message, "message")
          .map(BaaSRemoteFailure)
    }

  implicit def addRecipeRequestProto(implicit ev0: SerializersProvider): ProtoMap[AddRecipeRequest, protobuf.AddRecipeRequest] =
    new ProtoMap[AddRecipeRequest, protobuf.AddRecipeRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.AddRecipeRequest] =
        protobuf.AddRecipeRequest

      override def toProto(a: AddRecipeRequest): protobuf.AddRecipeRequest =
        protobuf.AddRecipeRequest(Some(ctxToProto(a.compiledRecipe)))

      override def fromProto(message: protobuf.AddRecipeRequest): Try[AddRecipeRequest] =
        versioned(message.compiledRecipe, "compiledRecipe")
          .flatMap(ctxFromProto(_))
          .map(AddRecipeRequest)
    }

  implicit def addRecipeResponseProto: ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] =
    new ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.AddRecipeResponse] =
        protobuf.AddRecipeResponse

      override def toProto(a: AddRecipeResponse): protobuf.AddRecipeResponse =
        protobuf.AddRecipeResponse(Some(a.recipeId))

      override def fromProto(message: protobuf.AddRecipeResponse): Try[AddRecipeResponse] =
        versioned(message.recipeId, "recipeId")
          .map(AddRecipeResponse)
    }
}
