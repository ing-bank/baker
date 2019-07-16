package com.ing.baker.runtime.akka.actor.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.types.Value
import com.ing.baker.runtime.akka.actor.{protobuf => proto}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.{EventMoment, RecipeInstanceState}

import scala.util.Try

class ProcessStateMapping extends ProtoMap[RecipeInstanceState, proto.ProcessState] {

    val companion = proto.ProcessState

    def toProto(a: RecipeInstanceState): proto.ProcessState = {
      val protoIngredients = a.ingredients.toSeq.map { case (name, value) =>
        proto.Ingredient(Some(name), None, Some(ctxToProto(value)))
      }
      proto.ProcessState(Some(a.recipeInstanceId), protoIngredients, a.events.map(ctxToProto(_)))
    }

    def fromProto(message: proto.ProcessState): Try[RecipeInstanceState] =
      for {
        recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        ingredients <- message.ingredients.toList.traverse[Try, (String, Value)] { i =>
          for {
            name <- versioned(i.name, "name")
            protoValue <- versioned(i.value, "value")
            value <- ctxFromProto(protoValue)
          } yield (name, value)
        }
        events <- message.events.toList.traverse (ctxFromProto(_))

      } yield RecipeInstanceState(recipeInstanceId, ingredients.toMap, events)
}
