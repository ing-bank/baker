package com.ing.baker.runtime.core.interations

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.types.{Type, Value}

trait InteractionImplementation {

  /**
    * The name of the interaction
    */
  val name: String

  /**
    * The required input.
    */
  val inputTypes: Seq[Type]

  /**
    * Executes the interaction.
    *
    * TODO input could be map instead of sequence??
    *
    * @param input
    * @return
    */
  def execute(interaction: InteractionTransition[_], input: Seq[Value]): Option[RuntimeEvent]
}
