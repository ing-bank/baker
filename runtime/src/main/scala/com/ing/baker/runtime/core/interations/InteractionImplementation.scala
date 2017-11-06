package com.ing.baker.runtime.core.interations

import java.lang.reflect.Type

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.types.Value
import com.ing.baker.runtime.core.RuntimeEvent

trait InteractionImplementation {

  val name: String

  val requiredIngredients: Seq[Type]

  val returnType: Type

  def isValidForInteraction(interaction: InteractionTransition[_]) : Boolean

  /**
    * Executes the interaction.
    *
    * TODO input could be map instead of sequence??
    *
    * @param input
    * @return
    */
  def execute(interaction: InteractionTransition[_], input: Seq[Value]): RuntimeEvent
}
