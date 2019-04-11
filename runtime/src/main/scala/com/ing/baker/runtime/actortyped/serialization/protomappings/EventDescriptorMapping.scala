package com.ing.baker.runtime.actortyped.serialization.protomappings

import cats.implicits._
import com.ing.baker.il
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ ctxToProto, ctxFromProto, versioned }
import com.ing.baker.runtime.actor.protobuf

import scala.util.Try

class EventDescriptorMapping extends ProtoMap[il.EventDescriptor, protobuf.EventDescriptor] {

  val companion = protobuf.EventDescriptor

  def toProto(event: il.EventDescriptor): protobuf.EventDescriptor = {
    val protoIngredients: Seq[protobuf.IngredientDescriptor] = event.ingredients.map(ctxToProto(_))
    protobuf.EventDescriptor(Some(event.name), protoIngredients)
  }

  def fromProto(message: protobuf.EventDescriptor): Try[il.EventDescriptor] =
    for {
      name <- versioned(message.name, "name")
      ingredients <- message.ingredients.toList.traverse[Try, il.IngredientDescriptor](ctxFromProto(_))
    } yield il.EventDescriptor(name, ingredients)

}
