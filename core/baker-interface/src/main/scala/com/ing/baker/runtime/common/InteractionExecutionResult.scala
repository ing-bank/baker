package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait InteractionExecutionResult extends LanguageApi{

  val isSuccess : Boolean

  val success : language.Option[_ <: InteractionExecutionResultSuccess]

  val failure : language.Option[_ <: InteractionExecutionResultFailure]

}

trait InteractionExecutionResultSuccess extends LanguageApi {
  val result: language.Option[_ <: EventInstance]
}

trait InteractionExecutionResultFailure extends LanguageApi  {
  val reason: InteractionExecutionFailureReason

  val interactionName: language.Option[String]
  /**
    * Only set if InteractionExecutionFailureReason == INTERACTION_EXECUTION_ERROR
    */
  val interactionExecutionErrorMessage : language.Option[String]

}
