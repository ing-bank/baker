package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.{Type, Value}

/**
  * Provides an implementation for an interaction.
  */
trait InteractionImplementation[F[_]] extends LanguageApi { self =>

  type Event <: RuntimeEvent { type Language = self.Language }

  /**
    * The name of the interaction
    */
  val name: String

  /**
    * The required input.
    */
  val input: language.Map[String, Type]

  /**
   * The required output.
   */
  val output: language.Option[language.Map[String, language.Map[String, Type]]]

  /**
    * Executes the interaction.
    */
  def execute(input: language.Map[String, Value]): F[language.Option[Event]]
}
