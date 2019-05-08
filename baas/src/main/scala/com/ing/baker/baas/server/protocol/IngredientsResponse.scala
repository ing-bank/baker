package com.ing.baker.baas.server.protocol

import com.ing.baker.types.Value

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.core.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.core.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class IngredientsResponse(ingredients: Map[String, Value]) extends BaasResponse

object IngredientsResponse {

  implicit def protoMap(implicit provider: SerializersProvider): ProtoMap[IngredientsResponse, protobuf.IngredientsResponse] =
    new ProtoMap[IngredientsResponse, protobuf.IngredientsResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.IngredientsResponse] =
        protobuf.IngredientsResponse

      override def toProto(a: IngredientsResponse): protobuf.IngredientsResponse =
        protobuf.IngredientsResponse(a.ingredients.map { case (name, value) => name -> ctxToProto(value) })

      override def fromProto(message: protobuf.IngredientsResponse): Try[IngredientsResponse] =
        for {
          ingredients <- message.ingredients.toList.traverse[Try, (String, Value)] {
            case (k, v) => ctxFromProto(v).map(k -> _)
          }
        } yield IngredientsResponse(ingredients.toMap)
    }
}
