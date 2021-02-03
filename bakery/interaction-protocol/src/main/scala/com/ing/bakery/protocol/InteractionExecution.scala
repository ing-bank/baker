package com.ing.bakery.protocol

import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.types.Type
import io.circe.Codec
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
  import com.ing.baker.types._

  implicit val recordTypeCodec: Codec[RecordType] = deriveCodec[RecordType]
  implicit val mapTypeCodec: Codec[MapType] = deriveCodec[MapType]
  implicit val enumTypeCodec: Codec[EnumType] = deriveCodec[EnumType]
  implicit val optionTypeCodec: Codec[OptionType] = deriveCodec[OptionType]
  implicit val recordFieldCcodec: Codec[RecordField] = deriveCodec[RecordField]
  implicit val recordValueCodec: Codec[RecordValue] = deriveCodec[RecordValue]
  implicit val listTypeCodec: Codec[ListType] = deriveCodec[ListType]
  implicit val listValueCodecc: Codec[ListValue] = deriveCodec[ListValue]

  implicit val primitiveTypeCodec: Codec[PrimitiveType] = deriveCodec[PrimitiveType]
  implicit val typeCodec: Codec[Type] =  deriveCodec[Type]

  implicit val instanceInterfaceCodec: Codec[Interaction] = deriveCodec[Interaction]
  implicit val ingredientInstanceCodec: Codec[IngredientInstance] = deriveCodec[IngredientInstance]

  implicit val failureReasonCodec: Codec[FailureReason] = deriveCodec[FailureReason]
  implicit val successCodec: Codec[Success] = deriveCodec[Success]
  implicit val failureCodec: Codec[Failure] = deriveCodec[Failure]
  implicit val eitherFailureOrSuccessCodec: Codec[Either[Failure, Success]] = deriveCodec[Either[Failure, Success]]
  implicit val executionResultEncoder: Codec[ExecutionResult] = deriveCodec[ExecutionResult]

}

object InteractionExecution {

  case class Interaction(id: String, name: String, input: List[Type])

  case class ExecutionResult(outcome: Either[Failure, Success])

  sealed trait Result
  case class Success(result: Option[EventInstance]) extends Result
  case class Failure(reason: FailureReason) extends Result

  sealed trait FailureReason
  case class InteractionError(message: String)  extends FailureReason
  case object NoInstanceFound extends FailureReason
  case object Timeout extends FailureReason
  case object BadIngredients extends FailureReason

}
