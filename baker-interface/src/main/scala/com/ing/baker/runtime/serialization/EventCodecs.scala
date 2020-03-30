package com.ing.baker.runtime.serialization

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance}
import com.ing.baker.types
import io.circe.Encoder._
import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._
import scala.collection.JavaConverters._

object EventCodecs {

  implicit val valuesEncoder: Encoder[types.Value] =
    Encoder.instance {
      case types.NullValue =>
        Json.Null
      case types.ListValue(entries) =>
        encodeList(valuesEncoder)(entries)
      case types.RecordValue(entries) =>
        encodeMap(KeyEncoder.encodeKeyString, valuesEncoder)(entries)
      case types.PrimitiveValue(Array(elements@_*)) =>
        encodeList(encodeString)(elements.map(_.toString).toList)
      case types.PrimitiveValue(value) =>
        encodeString(value.toString)
    }

  implicit val eventInstanceEncoder: Encoder[EventInstance] = deriveEncoder[EventInstance]
  implicit val rejectReasonEncoder: Encoder[RejectReason] = encodeString.contramap(_.toString)
  implicit val exceptionEncoder: Encoder[ExceptionStrategyOutcome] = deriveEncoder[ExceptionStrategyOutcome]
  implicit val throwableEncoder: Encoder[Throwable] = (throwable: Throwable) => Json.obj(("error", Json.fromString(throwable.getMessage)))
  implicit val compiledRecipeEncoder: Encoder[CompiledRecipe] =
    (recipe: CompiledRecipe) => Json.obj(
      ("name", Json.fromString(recipe.name)),
      ("recipeId", Json.fromString(recipe.recipeId)),
      ("validationErrors", recipe.getValidationErrors.asScala.asJson))


  implicit val bakerEventEncoder: Encoder[BakerEvent] = deriveEncoder[BakerEvent]
}