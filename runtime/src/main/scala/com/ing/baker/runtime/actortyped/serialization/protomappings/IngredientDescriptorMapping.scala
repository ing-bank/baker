package com.ing.baker.runtime.actortyped.serialization.protomappings

import com.ing.baker.il
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.{ toProto => ctxToProto, fromProto => ctxFromProto, versioned }
import com.ing.baker.runtime.actor.protobuf

import scala.util.Try

class IngredientDescriptorMapping extends ProtobufMapping[il.IngredientDescriptor] {

  type ProtoClass = protobuf.IngredientDescriptor

  def toProto(event: il.IngredientDescriptor): ProtoClass = {
    val `type` = ctxToProto(event.`type`)
    protobuf.IngredientDescriptor(Some(event.name), Some(`type`))
  }

  def fromProto(message: ProtoClass): Try[il.IngredientDescriptor] =
    for {
      name <- versioned(message.name, "name")
      ingredientTypeProto <- versioned(message.`type`, "type")
      ingredientType <- ctxFromProto(ingredientTypeProto)
    } yield il.IngredientDescriptor(name, ingredientType)

}

