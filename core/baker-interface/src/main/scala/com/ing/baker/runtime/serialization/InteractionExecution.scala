package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceInput}
import com.ing.baker.runtime.serialization.InteractionExecution.{Descriptor, ExecutionResult, Failure, FailureReason, Success}
import com.ing.baker.types.Type
import io.circe.{Codec, Decoder, Encoder, Json}
import io.circe.generic.semiauto.{deriveCodec, deriveDecoder, deriveEncoder}


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
  import com.ing.baker.runtime.serialization.JsonCodec._
  import com.ing.baker.runtime.serialization.JsonDecoders._
  import com.ing.baker.runtime.serialization.JsonEncoders._

  implicit val interactionExecutionDescriptorEncoder: Encoder[Descriptor] = deriveEncoder[Descriptor].mapJsonObject(_.filter(removeNulls))
  implicit val interactionExecutionDescriptorDecoder: Decoder[Descriptor] = deriveDecoder[Descriptor]
  implicit val failureReasonCodec: Codec[FailureReason] = deriveCodec[FailureReason]
  implicit val successCodec: Codec[Success] = deriveCodec[Success]
  implicit val failureCodec: Codec[Failure] = deriveCodec[Failure]
  implicit val eitherFailureOrSuccessCodec: Codec[Either[Failure, Success]] = deriveCodec[Either[Failure, Success]]
  implicit val executionResultEncoder: Codec[ExecutionResult] = deriveCodec[ExecutionResult]
}

object InteractionExecution {

  case class Descriptor(id: String, name: String, input: Seq[InteractionInstanceInput], output: Option[Map[String, Map[String, Type]]])
  case class ExecutionResult(outcome: Either[Failure, Success])

  sealed trait Result
  case class Success(result: Option[EventInstance]) extends Result
  case class Failure(reason: FailureReason) extends Result

  sealed trait FailureReason
  case class InteractionError(interactionName: String, message: String)  extends FailureReason
  case object NoInstanceFound extends FailureReason
  case object Timeout extends FailureReason
  case object BadIngredients extends FailureReason

}
