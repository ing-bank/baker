package com.ing.baker.runtime.serialization.protomappings

import cats.effect.ExitCode.Success
import cats.implicits._
import com.ing.baker.types.Value
import com.ing.baker.runtime.akka.actor.{protobuf => proto}
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.{EventMoment, RecipeInstanceState}
import com.ing.baker.runtime.serialization.ProtoMap

import scala.util.Try

class ProcessStateMapping extends ProtoMap[RecipeInstanceState, proto.ProcessState] {

    val companion = proto.ProcessState

    def toProto(a: RecipeInstanceState): proto.ProcessState = {
      val protoIngredients = a.ingredients.toSeq.map { case (name, value) =>
        proto.Ingredient(Some(name), None, Some(ctxToProto(value)))
      }
      proto.ProcessState(Some(a.recipeId), Some(a.recipeInstanceId), protoIngredients, a.recipeInstanceMetadata,  a.events.map(ctxToProto(_)))
    }

    def fromProto(message: proto.ProcessState): Try[RecipeInstanceState] =
      for {
        recipeId <- Try(message.recipeId.getOrElse(""))
        recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        ingredients <- message.ingredients.toList.traverse[Try, (String, Value)] { i =>
          for {
            name <- versioned(i.name, "name")
            protoValue <- versioned(i.value, "value")
            value <- ctxFromProto(protoValue)
          } yield (name, value)
        }
        recipeInstanceMetaData = message.recipeInstanceMetadata
        events <- message.events.toList.traverse (ctxFromProto(_))

      } yield RecipeInstanceState(recipeId, recipeInstanceId, ingredients.toMap, recipeInstanceMetaData, events)
}
