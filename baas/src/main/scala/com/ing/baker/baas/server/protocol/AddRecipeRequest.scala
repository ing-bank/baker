package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.core.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try
import com.ing.baker.il.CompiledRecipe

case class AddRecipeRequest(compiledRecipe: CompiledRecipe) extends BaasRequest

object AddRecipeRequest {

  implicit def protoMap(implicit provider: SerializersProvider): ProtoMap[AddRecipeRequest, protobuf.AddRecipeRequest] =
    new ProtoMap[AddRecipeRequest, protobuf.AddRecipeRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.AddRecipeRequest] =
        protobuf.AddRecipeRequest

      override def toProto(a: AddRecipeRequest): protobuf.AddRecipeRequest =
        protobuf.AddRecipeRequest(Some(ctxToProto(a.compiledRecipe)))

      override def fromProto(message: protobuf.AddRecipeRequest): Try[AddRecipeRequest] =
        for {
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield AddRecipeRequest(compiledRecipe)
    }
}
