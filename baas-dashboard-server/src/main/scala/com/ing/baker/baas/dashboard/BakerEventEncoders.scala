package com.ing.baker.baas.dashboard

import com.ing.baker.runtime.scaladsl.{EventReceived, EventRejected, InteractionCompleted, InteractionFailed, InteractionStarted, RecipeAdded, RecipeInstanceCreated}
import com.ing.baker.types
import io.circe.{Decoder, DecodingFailure, Encoder, Json, JsonObject, KeyDecoder, KeyEncoder}
import io.circe.Encoder._
import io.circe.Decoder._
import io.circe.syntax._
import io.circe.generic.auto._

object BakerEventEncoders {

  implicit def ValuesEncoder: Encoder[types.Value] =
    Encoder.instance {
      case types.NullValue =>
        Json.Null
      case types.ListValue(entries) =>
        encodeList(ValuesEncoder)(entries)
      case types.RecordValue(entries) =>
        encodeMap(KeyEncoder.encodeKeyString, ValuesEncoder)(entries)
      case types.PrimitiveValue(value) =>
        encodeString(value.toString)
    }

  implicit def ValuesDecoder: Decoder[types.Value] = {
    def list: Decoder[types.Value] = decodeList(ValuesDecoder).map(types.ListValue)

    def record: Decoder[types.Value] = decodeMap(KeyDecoder.decodeKeyString, ValuesDecoder).map(types.RecordValue)

    def primitive: Decoder[types.Value] = decodeString.map(types.PrimitiveValue)

    def nullDecoder: Decoder[types.Value] = Decoder.instance[types.Value] { hcursor =>
      if (hcursor.value.isNull) Right(types.NullValue)
      else Left(DecodingFailure("Not a baker Null Value", hcursor.history))
    }

    list.or(record).or(primitive).or(nullDecoder)
  }

  implicit val ThrowableEncoder: Encoder[Throwable] =
    Encoder.instance { e =>
      Encoder.encodeString(e.getMessage)
    }

  implicit val ThrowableDecoder: Decoder[Throwable] =
    Decoder.decodeString.map(e => new RuntimeException(e))

  implicit val EventReceivedEncoder: Encoder[EventReceived] =
    Encoder.instance { event =>
      encodeJsonObject(JsonObject(
        "type" -> encodeString("BakerEvent"),
        "BakerEvent" -> encodeString("EventReceived"),
        "timeStamp" -> encodeLong(event.timeStamp),
        "recipeName" -> encodeString(event.recipeName),
        "recipeId" -> encodeString(event.recipeId),
        "recipeInstanceId" -> encodeString(event.recipeInstanceId),
        "correlationId" -> encodeOption(encodeString)(event.correlationId),
        "event" -> event.event.asJson
      ))
    }

  //implicit val eventRejectedEncoder: Encoder[EventRejected] =

  implicit val EventRejectedEncoder: Encoder[InteractionFailed] =
    Encoder.instance { event =>
      encodeJsonObject(JsonObject(
        "type" -> "BakerEvent".asJson,
        "BakerEvent" -> "InteractionFailed".asJson,
        "timeStamp" -> event.timeStamp.asJson,
        "duration" -> event.duration.asJson,
        "recipeName" -> event.recipeName.asJson,
        "recipeId" -> event.recipeId.asJson,
        "recipeInstanceId" -> event.recipeInstanceId.asJson,
        "interactionName" -> event.interactionName.asJson,
        "failureCount" -> event.failureCount.asJson,
        "throwable" -> event.throwable.asJson,
        "exceptionStrategyOutcome" -> event.exceptionStrategyOutcome.asJson
      ))
    }

  implicit val InteractionStartedEncoder: Encoder[InteractionStarted] =
    Encoder.instance { event =>
      encodeJsonObject(JsonObject(
        "type" -> encodeString("BakerEvent"),
        "BakerEvent" -> encodeString("InteractionStarted"),
        "timeStamp" -> event.timeStamp.asJson,
        "recipeName" -> event.recipeName.asJson,
        "recipeId" -> event.recipeId.asJson,
        "recipeInstanceId" -> event.recipeInstanceId.asJson,
        "interactionName" ->event.interactionName.asJson
      ))
    }

  implicit val InteractionCompletedEncoder: Encoder[InteractionCompleted] =
    Encoder.instance { event =>
      encodeJsonObject(JsonObject(
        "type" -> encodeString("BakerEvent"),
        "BakerEvent" -> encodeString("InteractionCompleted"),
        "timeStamp" -> event.timeStamp.asJson,
        "duration" -> event.duration.asJson,
        "recipeName" -> event.recipeName.asJson,
        "recipeId" -> event.recipeId.asJson,
        "recipeInstanceId" -> event.recipeInstanceId.asJson,
        "interactionName" -> event.interactionName.asJson,
        "event" -> event.event.asJson
      ))
    }

  implicit val RecipeInstanceCreatedEncoder: Encoder[RecipeInstanceCreated] =
    Encoder.instance { event =>
      encodeJsonObject(JsonObject(
        "type" -> encodeString("BakerEvent"),
        "BakerEvent" -> encodeString("RecipeInstanceCreated"),
        "timeStamp" -> event.timeStamp.asJson,
        "recipeId" -> event.recipeId.asJson,
        "recipeName" -> event.recipeName.asJson,
        "recipeInstanceId" ->event.recipeInstanceId.asJson
      ))
    }

  implicit val RecipeAddedEncoder: Encoder[RecipeAdded] =
    Encoder.instance { event =>
      encodeJsonObject(JsonObject(
        "type" -> encodeString("BakerEvent"),
        "BakerEvent" -> encodeString("RecipeAdded"),
        "recipeName" -> event.recipeName.asJson,
        "recipeId" -> event.recipeId.asJson,
        "date" -> event.date.asJson,
        "visualization" -> event.compiledRecipe.getRecipeVisualization.asJson
      ))
    }
}
