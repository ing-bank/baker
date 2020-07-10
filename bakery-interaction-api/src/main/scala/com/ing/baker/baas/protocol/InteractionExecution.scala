package com.ing.baker.baas.protocol

import com.ing.baker.runtime.akka.actor.protobuf.PrimitiveType
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance, IngredientInstance}
import com.ing.baker.types.{Bool, Type}
import io.circe.CursorOp.Field
import io.circe.{Codec, Decoder, DecodingFailure, Encoder, HCursor, Json}
import io.circe.generic.semiauto.deriveCodec
/**
  * Protocol executed after a match between a QuestMandate and InteractionAgent has been made and after both
  * have committed.
  *
  * A simple request from the manager to the agent for execution with specific ingredients is done using the
  * ExecuteInstance message, the outcome comes in the form of either the response messages InstanceExecutedSuccessfully,
  * InstanceExecutionFailed or InvalidExecution
  *
  */

object InteractionExecutionJsonCodecs {

  import com.ing.baker.runtime.serialization.JsonEncoders._
  import com.ing.baker.runtime.serialization.JsonDecoders._
  import InteractionExecution._

  implicit val typeCodec: Codec[Type] = Codec.from(
   Decoder.instance[Type] {
     (c: HCursor) => for {
       typeAsString <- c.as[String]
       result <- Type.fromString(typeAsString).left.map(DecodingFailure(_, List.empty))
     } yield result
   },
    Encoder.instance[Type](
      x => Json.fromString(x.toString)
    )
  )

  implicit val instanceInterfaceCodec: Codec[Interaction] = deriveCodec[Interaction]
  implicit val ingredientInstanceCodec: Codec[IngredientInstance] = deriveCodec[IngredientInstance]

  implicit val failureReasonCodec: Codec[FailureReason] = deriveCodec[FailureReason]
  implicit val successCodec: Codec[Success] = deriveCodec[Success]
  implicit val failureCodec: Codec[Failure] = deriveCodec[Failure]
}

object InteractionExecution {

  case class Interaction(id: String, name: String, input: Seq[Type])

  sealed trait Result
  case class Success(result: Option[EventInstance]) extends Result
  case class Failure(reason: FailureReason) extends Result

  sealed trait FailureReason
  case class InteractionError(message: String)  extends FailureReason
  case object NoInstanceFound extends FailureReason
  case object Timeout extends FailureReason
  case object BadIngredients extends FailureReason

}
