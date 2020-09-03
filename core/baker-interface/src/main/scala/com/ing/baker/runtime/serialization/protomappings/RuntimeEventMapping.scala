package com.ing.baker.runtime.serialization.protomappings
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.types.Value

import scala.util.Try

class RuntimeEventMapping extends ProtoMap[EventInstance, protobuf.RuntimeEvent] {

  val companion = protobuf.RuntimeEvent

  override def toProto(a: EventInstance): protobuf.RuntimeEvent = {
    val protoIngredients = a.providedIngredients.map { case (name, value) =>
      protobuf.Ingredient(Some(name), None, Some(ctxToProto(value)))
    }
    protobuf.RuntimeEvent(Some(a.name), protoIngredients.toSeq)
  }

  override def fromProto(message: protobuf.RuntimeEvent): Try[EventInstance] =
    for {
      name <- versioned(message.name, "name")
      ingredients <- message.providedIngredients.toList.traverse[Try, (String, Value)] { i =>
        for {
          name <- versioned(i.name, "name")
          protoValue <- versioned(i.value, "value")
          value <- ctxFromProto(protoValue)
        } yield (name, value)
      }
    } yield EventInstance(name, ingredients.toMap)
}
