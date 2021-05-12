package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Type

/**
  * Provides an implementation for an interaction.
  */
trait InteractionInstanceDescriptor extends LanguageApi { self =>

  type Ingredient <: IngredientInstance { type Language = self.Language }

  type Event <: EventInstance { type Language = self.Language }

  type Input <: InteractionInstanceInput { type Language = self.Language }

  /**
    * The name of the interaction
    */
  val name: String

  /**
    * The input description, used to match on different versions of the implementation.
    */
  val input: language.Seq[Input]

  /**
   * The output description, used to match on different versions of the implementation.
   */
  val output: language.Option[language.Map[String, language.Map[String, Type]]]
}
