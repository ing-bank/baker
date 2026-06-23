package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.{InteractionExecutionFailureReason, InteractionExecutionResultFailure, InteractionExecutionResultSuccess}
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.javadsl.{InteractionExecutionResult => JavaInteractionExecutionResult}
import com.ing.baker.runtime.serialization.InteractionExecution

import java.util.Optional

case class InteractionExecutionResult(either: Either[InteractionExecutionResult.Failure, InteractionExecutionResult.Success]) extends common.InteractionExecutionResult with ScalaApi {
  override val isSuccess: Boolean = either.isRight
  override val success: Option[InteractionExecutionResult.Success] = either.toOption
  override val failure: Option[InteractionExecutionResult.Failure] = either.swap.toOption

  def asJava: JavaInteractionExecutionResult =
    JavaInteractionExecutionResult(Optional.ofNullable(success.map(_.asJava).orNull), Optional.ofNullable(failure.map(_.asJava).orNull))

  def toSerializationInteractionExecutionResult : InteractionExecution.ExecutionResult =
    InteractionExecution.ExecutionResult(either match {
      case Left(value) => Left(value.toSerializationInteractionExecutionFailure)
      case Right(value) => Right(value.toSerializationInteractionExecutionSuccess)
    })
}

object InteractionExecutionResult {
  case class Success(override val result: Option[EventInstance]) extends InteractionExecutionResultSuccess with ScalaApi {
    def asJava : JavaInteractionExecutionResult.Success =
      JavaInteractionExecutionResult.Success(Optional.ofNullable(result.map(_.asJava).orNull))
    def toSerializationInteractionExecutionSuccess : InteractionExecution.Success =
      InteractionExecution.Success(result)
  }
  case class Failure(override val reason: InteractionExecutionFailureReason,
                     override val interactionName: Option[String],
                     override val interactionExecutionErrorMessage: Option[String]) extends InteractionExecutionResultFailure with ScalaApi {
    def asJava : JavaInteractionExecutionResult.Failure = JavaInteractionExecutionResult.Failure(
      reason = reason,
      interactionName = Optional.ofNullable(interactionName.orNull),
      interactionExecutionErrorMessage = Optional.ofNullable(interactionExecutionErrorMessage.orNull))

    def toSerializationInteractionExecutionFailure : InteractionExecution.Failure =
      InteractionExecution.Failure(reason match {
        case InteractionExecutionFailureReason.INTERACTION_EXECUTION_ERROR => InteractionExecution.InteractionError(interactionName.getOrElse("Unknown interaction name"), interactionExecutionErrorMessage.getOrElse("No error message found"))
        case InteractionExecutionFailureReason.INTERACTION_NOT_FOUND => InteractionExecution.NoInstanceFound
        case InteractionExecutionFailureReason.TIMEOUT => InteractionExecution.Timeout
        case InteractionExecutionFailureReason.BAD_INGREDIENTS => InteractionExecution.BadIngredients
      })
  }
}

