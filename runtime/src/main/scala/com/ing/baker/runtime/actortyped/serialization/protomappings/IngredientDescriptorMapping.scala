package com.ing.baker.runtime.actortyped.serialization.protomappings

import com.ing.baker.il
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ ctxToProto, ctxFromProto, versioned }
import com.ing.baker.runtime.actor.protobuf

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

