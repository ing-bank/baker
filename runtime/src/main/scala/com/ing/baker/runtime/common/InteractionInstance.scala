package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.{Type, Value}

/**
  * Provides an implementation for an interaction.
  */
trait InteractionInstance[F[_]] extends LanguageApi { self =>

  type Ingredient <: IngredientInstance { type Language = self.Language }

  type Event <: EventInstance { type Language = self.Language }

  /**
    * The name of the interaction
    */
  val name: String

  /**
    * The input description, used to match on different versions of the implementation.
    */
  val input: language.Seq[Type]

  /**
   * The output description, used to match on different versions of the implementation.
   */
  val output: language.Option[language.Map[String, language.Map[String, Type]]]

  /**
    * Executes the interaction.
    *
    * Note: The input is a sequence of ingredients because there can be 2 ingredients with the same name, e.g. when
    * 2 ingredients get renamed to the same name.
    */
  def execute(input: language.Seq[Ingredient]): F[language.Option[Event]]
}
