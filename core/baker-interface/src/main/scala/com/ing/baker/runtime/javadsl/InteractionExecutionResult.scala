package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.{InteractionExecutionFailureReason, InteractionExecutionResultFailure, InteractionExecutionResultSuccess}
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.scaladsl.{InteractionExecutionResult => ScalaInteractionExecutionResult}

import java.util.Optional

case class InteractionExecutionResult(
  override val success: Optional[InteractionExecutionResult.Success],
  override val failure: Optional[InteractionExecutionResult.Failure]) extends common.InteractionExecutionResult with JavaApi {

  override val isSuccess: Boolean = success.isPresent
  val getSuccess: Optional[InteractionExecutionResult.Success] = success
  val getFailure: Optional[InteractionExecutionResult.Failure] = failure

  def asScala: ScalaInteractionExecutionResult =
    if (isSuccess)
      ScalaInteractionExecutionResult(Right(ScalaInteractionExecutionResult.Success(Option(getSuccess.get().result.orElse(null)).map(_.asScala))))
    else
      ScalaInteractionExecutionResult(Left(ScalaInteractionExecutionResult.Failure(getFailure.get().reason, Option(getFailure.get().interactionName.orElse(null)), Option(getFailure.get().interactionExecutionErrorMessage.orElse(null)))))
}

object InteractionExecutionResult {
  case class Success(override val result: Optional[EventInstance]) extends InteractionExecutionResultSuccess with JavaApi
  case class Failure(override val reason: InteractionExecutionFailureReason,
                     override val interactionName: Optional[String],
                     override val interactionExecutionErrorMessage: Optional[String]) extends InteractionExecutionResultFailure with JavaApi
}
