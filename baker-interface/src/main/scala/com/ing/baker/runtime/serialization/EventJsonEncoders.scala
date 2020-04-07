package com.ing.baker.runtime.serialization

import java.util.Base64

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance}
import com.ing.baker.types
import io.circe.Encoder._
import io.circe._
import io.circe.generic.semiauto._
import io.circe.syntax._

import scala.collection.JavaConverters._

object EventJsonEncoders {

  private[serialization] val typeFieldName: String = "typ"
  private[serialization] val subTypeFieldName: String = "styp"
  private[serialization] val valueFieldName: String = "val"

  private[serialization] val byteArraySubtype: String = "ByteArray"

  private[serialization] val nullValueType: Int = 0
  private[serialization] val listValueType: Int = 1
  private[serialization] val recordValueType: Int = 2
  private[serialization] val primitiveValueType: Int = 3

  implicit val valuesEncoder: Encoder[types.Value] =
    Encoder.instance {
      case types.NullValue =>
        Json.fromFields(List((typeFieldName, nullValueType.asJson)))
      case types.ListValue(entries) =>
        Json.fromFields(List(
          (typeFieldName, listValueType.asJson),
          (valueFieldName, encodeList(valuesEncoder)(entries))))
      case types.RecordValue(entries) =>
        Json.fromFields(List(
          (typeFieldName, recordValueType.asJson),
          (valueFieldName, encodeMap(KeyEncoder.encodeKeyString, valuesEncoder)(entries))))
      case types.PrimitiveValue(value) =>
        val (subType, realValue) = value match {
          case bytes: Array[Byte] =>
            (byteArraySubtype, Base64.getEncoder.encodeToString(bytes))
          case _ => (value.getClass.getName, value.toString)
        }

        Json.fromFields(List(
          (typeFieldName, primitiveValueType.asJson),
          (subTypeFieldName, subType.asJson),
          (valueFieldName, realValue.asJson)))
    }

  implicit val eventInstanceEncoder: Encoder[EventInstance] = deriveEncoder[EventInstance]
  implicit val rejectReasonEncoder: Encoder[RejectReason] = encodeString.contramap(_.toString)
  implicit val exceptionEncoder: Encoder[ExceptionStrategyOutcome] = deriveEncoder[ExceptionStrategyOutcome]
  implicit val throwableEncoder: Encoder[Throwable] = (throwable: Throwable) => Json.obj(("error", Json.fromString(throwable.getMessage)))
  implicit val compiledRecipeEncoder: Encoder[CompiledRecipe] =
  // TODO: write PetriNet and Marking to json
    (recipe: CompiledRecipe) => Json.obj(
      ("name", Json.fromString(recipe.name)),
      ("recipeId", Json.fromString(recipe.recipeId)),
      ("validationErrors", recipe.getValidationErrors.asScala.asJson))

  implicit val bakerEventEncoder: Encoder[BakerEvent] = deriveEncoder[BakerEvent]
}