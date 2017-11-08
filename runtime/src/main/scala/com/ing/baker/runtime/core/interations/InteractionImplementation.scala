package com.ing.baker.runtime.core.interations

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.types.Value

trait InteractionImplementation {

  val name: String

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
