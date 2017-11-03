package com.ing.baker.runtime.core.interations

import java.lang.reflect.Type

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.types.Value

trait InteractionImplementation {

  val name: String

  val requiredIngredients: Seq[Type]

  val returnType: Type

  def isValidForInteraction(interaction: InteractionTransition[_]) : Boolean

  /**
    * Executes the interaction.
    *
    * @param input
    * @return
    */
  def execute(input: Seq[Value]): Value
}
