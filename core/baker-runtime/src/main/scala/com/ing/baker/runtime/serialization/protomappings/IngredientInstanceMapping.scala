package com.ing.baker.runtime.serialization.protomappings

import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.scaladsl.IngredientInstance
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.serialization.ProtoMap

import scala.util.Try

class IngredientInstanceMapping extends ProtoMap[IngredientInstance, protobuf.Ingredient] {

  val companion = protobuf.Ingredient

  override def toProto(data: IngredientInstance): protobuf.Ingredient =
    protobuf.Ingredient(Option(data.name), None, Some(ctxToProto(data.value)))

  override def fromProto(message: protobuf.Ingredient): Try[IngredientInstance] =
    for {
      name <- versioned(message.name, "name")
      valueProto <- versioned(message.value, "value")
      value <- ctxFromProto(valueProto)
    } yield IngredientInstance(name, value)

}
