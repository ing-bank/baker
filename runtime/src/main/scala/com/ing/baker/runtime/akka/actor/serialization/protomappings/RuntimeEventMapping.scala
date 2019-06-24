package com.ing.baker.runtime.akka.actor.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.RuntimeEvent
import com.ing.baker.types.Value

import scala.util.Try

class RuntimeEventMapping extends ProtoMap[RuntimeEvent, protobuf.RuntimeEvent] {

  val companion = protobuf.RuntimeEvent

  override def toProto(a: RuntimeEvent): protobuf.RuntimeEvent = {
    val protoIngredients = a.providedIngredients.map { case (name, value) =>
      protobuf.Ingredient(Some(name), None, Some(ctxToProto(value)))
    }
    protobuf.RuntimeEvent(Some(a.name), protoIngredients.toSeq)
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
    } yield RuntimeEvent(name, ingredients.toMap)
}
