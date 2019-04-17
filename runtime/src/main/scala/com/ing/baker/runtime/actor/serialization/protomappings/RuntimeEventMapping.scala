package com.ing.baker.runtime.actor.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.serialization.ProtoMap
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.types.Value
import com.ing.baker.runtime.actor.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}

import scala.util.Try

class RuntimeEventMapping extends ProtoMap[RuntimeEvent, protobuf.RuntimeEvent] {

  val companion = protobuf.RuntimeEvent

  override def toProto(a: RuntimeEvent): protobuf.RuntimeEvent = {
    val protoIngredients = a.providedIngredients.map { case (name, value) =>
      protobuf.Ingredient(Some(name), None, Some(ctxToProto(value)))
    }
    protobuf.RuntimeEvent(Some(a.name), protoIngredients)
  }

  override def fromProto(message: protobuf.RuntimeEvent): Try[RuntimeEvent] =
    for {
      name <- versioned(message.name, "name")
      ingredients <- message.providedIngredients.toList.traverse[Try, (String, Value)] { i =>
        for {
          name <- versioned(i.name, "name")
          protoValue <- versioned(i.value, "value")
          value <- ctxFromProto(protoValue)
        } yield (name, value)
      }
    } yield RuntimeEvent(name, ingredients)
}
