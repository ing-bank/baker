package com.ing.baker.runtime.serialization.protomappings
import com.ing.baker.il
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap

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
