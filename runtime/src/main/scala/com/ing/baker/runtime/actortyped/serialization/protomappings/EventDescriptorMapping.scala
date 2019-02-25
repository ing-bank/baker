package com.ing.baker.runtime.actortyped.serialization.protomappings

import cats.implicits._
import com.ing.baker.il
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.{ toProto => ctxToProto, fromProto => ctxFromProto, versioned }
import com.ing.baker.runtime.actor.protobuf

import scala.util.Try

class EventDescriptorMapping extends ProtobufMapping[il.EventDescriptor] {

  type ProtoClass = protobuf.EventDescriptor

  def toProto(event: il.EventDescriptor): ProtoClass = {
    val protoIngredients: Seq[protobuf.IngredientDescriptor] = event.ingredients.map(ctxToProto(_))
    protobuf.EventDescriptor(Some(event.name), protoIngredients)
  }

  def fromProto(message: ProtoClass): Try[il.EventDescriptor] =
    for {
      name <- versioned(message.name, "name")
      ingredients <- message.ingredients.toList.traverse[Try, il.IngredientDescriptor](ctxFromProto(_))
    } yield il.EventDescriptor(name, ingredients)

}
