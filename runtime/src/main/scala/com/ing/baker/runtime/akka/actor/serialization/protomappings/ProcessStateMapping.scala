package com.ing.baker.runtime.akka.actor.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.types.Value
import com.ing.baker.runtime.akka.actor.{protobuf => proto}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.ProcessState

import scala.util.Try

class ProcessStateMapping extends ProtoMap[ProcessState, proto.ProcessState] {

    val companion = proto.ProcessState

    def toProto(a: ProcessState): proto.ProcessState = {
      val protoIngredients = a.ingredients.toSeq.map { case (name, value) =>
        proto.Ingredient(Some(name), None, Some(ctxToProto(value)))
      }
      proto.ProcessState(Some(a.processId), protoIngredients, a.events.map(ctxToProto(_)))
    }

    def fromProto(message: proto.ProcessState): Try[ProcessState] =
      for {
        processId <- versioned(message.processId, "processId")
        ingredients <- message.ingredients.toList.traverse[Try, (String, Value)] { i =>
          for {
            name <- versioned(i.name, "name")
            protoValue <- versioned(i.value, "value")
            value <- ctxFromProto(protoValue)
          } yield (name, value)
        }
      } yield ProcessState(processId, ingredients.toMap, message.events.map(ctxFromProto(_).get))
}
