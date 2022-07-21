package com.ing.baker.runtime.serialization

import java.util.Base64

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.common.{BakerException, RejectReason, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.types._
import com.typesafe.scalalogging.LazyLogging
import io.circe.CursorOp.DownField
import io.circe.Decoder._
import io.circe.KeyDecoder.decodeKeyString
import io.circe._
import io.circe.generic.semiauto._
import scalax.collection.immutable.Graph
import com.ing.baker.runtime.serialization.JsonCodec._

object JsonDecoders extends LazyLogging {

  implicit val valuesDecoder: Decoder[Value] = (c: HCursor) => {
    c.downField(typeFieldName).as[Int].flatMap(
      typ =>
        if (typ == nullValueType)
          Right(NullValue)
        else if (typ == listValueType) {
          c.downField(valueFieldName)
            .as[List[Value]](Decoder.decodeList(valuesDecoder))
            .map(ListValue.apply)
        } else if (typ == recordValueType) {
          c.downField(valueFieldName)
            .as[Map[String, Value]](Decoder.decodeMap[String, Value](decodeKeyString, valuesDecoder))
            .map(RecordValue.apply)
        } else {
          try {
            for {
              sTyp <- c.downField(subTypeFieldName).as[String]
              value <- c.downField(valueFieldName).as[String]
            } yield {
              if (sTyp == byteArraySubtype) {
                PrimitiveValue(Base64.getDecoder.decode(value))
              } else if (sTyp == "java.lang.String") {
                PrimitiveValue(value)
              } else if (sTyp == "java.lang.Character") {
                PrimitiveValue(Character.valueOf(value.headOption.getOrElse('\u0000')))
              } else if (sTyp == "java.math.BigInteger") {
                PrimitiveValue(new java.math.BigInteger(value))
              } else if (sTyp == "java.math.BigDecimal") {
                PrimitiveValue(new java.math.BigDecimal(value))
              } else if (sTyp == "scala.math.BigInt") {
                PrimitiveValue(BigInt(value))
              } else if (sTyp == "scala.math.BigDecimal") {
                PrimitiveValue(BigDecimal(value))
              } else {
                val result = Class
                  .forName(sTyp)
                  .getDeclaredMethod("valueOf", classOf[String])
                  .invoke(null, value)

                PrimitiveValue(result)
              }
            }
          } catch {
            case ex: Exception =>
              logger.error("Unable parse the type", ex)
              Left(DecodingFailure(s"Unsupported type",
                List(DownField(subTypeFieldName), DownField(valueFieldName))))
          }
        }
    )
  }

  implicit val encodedRecipeDecoder: Decoder[EncodedRecipe] = deriveDecoder[EncodedRecipe]

  implicit val rejectReasonDecoder: Decoder[RejectReason] = decodeString.map(RejectReason.valueOf)
  implicit val exceptionDecoder: Decoder[ExceptionStrategyOutcome] = deriveDecoder[ExceptionStrategyOutcome]
  implicit val throwableDecoder: Decoder[Throwable] = decodeString.map(new RuntimeException(_))

  implicit val compiledRecipeDecoder: Decoder[CompiledRecipe] = (c: HCursor) => {
    for {
      name <- c.downField("name").as[String]
      recipeId <- c.downField("recipeId").as[String]
      validationErrors <- c.downField("validationErrors").as[List[String]]
    } yield {
      // TODO: read PetriNet and Marking from json
      CompiledRecipe(name, recipeId, new PetriNet(Graph.empty), Marking.empty, validationErrors, Option.empty, Option.empty)
    }
  }
  implicit val eventInstanceDecoder: Decoder[EventInstance] = deriveDecoder[EventInstance]
  implicit val bakerEventDecoder: Decoder[BakerEvent] = deriveDecoder[BakerEvent]
  implicit val recipeInformationDecoder: Decoder[RecipeInformation] = deriveDecoder[RecipeInformation]
  implicit val recipeInstanceStateDecoder: Decoder[RecipeInstanceState] = deriveDecoder[RecipeInstanceState]
  implicit val recipeInstanceMetadataDecoder: Decoder[RecipeInstanceMetadata] = deriveDecoder[RecipeInstanceMetadata]

  implicit val sensoryEventStatusDecoder: Decoder[SensoryEventStatus] = Decoder.decodeString.map(SensoryEventStatus.valueOf)
  implicit val sensoryEventResultDecoder: Decoder[SensoryEventResult] = deriveDecoder[SensoryEventResult]

  implicit val eventMomentDecoder: Decoder[EventMoment] = deriveDecoder[EventMoment]
  implicit val bakerResultDecoder: Decoder[BakerResult] = deriveDecoder[BakerResult]

  implicit val bakerExceptionDecoder: Decoder[BakerException] = (c: HCursor) => {
    for {
      message <- c.downField("message").as[String]
      enum <- c.downField("enum").as[Int]
    } yield BakerException.decodeOrUnknownBakerException(message, `enum`)
  }

  implicit val interactionInstanceInputDecoder: Decoder[InteractionInstanceInput] = deriveDecoder[InteractionInstanceInput]
  implicit val interactionInstanceDescriptorDecoder: Decoder[InteractionInstanceDescriptor] = deriveDecoder[InteractionInstanceDescriptor]
}
