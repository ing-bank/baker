package com.ing.baker.runtime.serialization.protomappings

import com.ing.baker.il
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap

import scala.util.Try

class IngredientDescriptorMapping extends ProtoMap[il.IngredientDescriptor, protobuf.IngredientDescriptor] {

  val companion = protobuf.IngredientDescriptor

  def toProto(event: il.IngredientDescriptor): protobuf.IngredientDescriptor = {
    val `type` = ctxToProto(event.`type`)
    protobuf.IngredientDescriptor(Some(event.name), Some(`type`))
  }

  def fromProto(message: protobuf.IngredientDescriptor): Try[il.IngredientDescriptor] =
    for {
      name <- versioned(message.name, "name")
      ingredientTypeProto <- versioned(message.`type`, "type")
      ingredientType <- ctxFromProto(ingredientTypeProto)
    } yield il.IngredientDescriptor(name, ingredientType)

}

