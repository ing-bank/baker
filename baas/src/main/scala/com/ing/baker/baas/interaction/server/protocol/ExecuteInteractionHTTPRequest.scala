package com.ing.baker.baas.interaction.server.protocol

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.baas.server.protocol.BaasRequest
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.runtime.scaladsl.IngredientInstance
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class ExecuteInteractionHTTPRequest(input: Seq[IngredientInstance]) extends BaasRequest

object ExecuteInteractionHTTPRequest {

  implicit def protoMap: ProtoMap[ExecuteInteractionHTTPRequest, protobuf.ExecuteInteractionHTTPRequest] =
    new ProtoMap[ExecuteInteractionHTTPRequest, protobuf.ExecuteInteractionHTTPRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.ExecuteInteractionHTTPRequest] =
        protobuf.ExecuteInteractionHTTPRequest

      override def toProto(a: ExecuteInteractionHTTPRequest): protobuf.ExecuteInteractionHTTPRequest =
        protobuf.ExecuteInteractionHTTPRequest(a.input.map(v => com.ing.baker.runtime.akka.actor.protobuf.Ingredient(Some(v.name), None, Some(ctxToProto(v.value)))))

      override def fromProto(message: protobuf.ExecuteInteractionHTTPRequest): Try[ExecuteInteractionHTTPRequest] =
        for {
          input <- message.ingredient.toList.traverse { protoIngredient =>
            for {
              name <- versioned(protoIngredient.name, "name")
              valueProto <- versioned(protoIngredient.value, "value")
              value <- ctxFromProto(valueProto)
            } yield IngredientInstance(name, value)
          }
        } yield ExecuteInteractionHTTPRequest(input)
    }
}
