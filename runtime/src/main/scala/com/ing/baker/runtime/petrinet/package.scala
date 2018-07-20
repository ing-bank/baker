package com.ing.baker.runtime

import com.ing.baker.il.petrinet.{InteractionTransition, Place}
import com.ing.baker.petrinet.api.{Marking, MultiSet, _}
import com.ing.baker.runtime.core.RuntimeEvent

package object petrinet {
  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    */
  def createProducedMarking(interaction: InteractionTransition, outAdjacent: MultiSet[Place[_]]): RuntimeEvent => Marking[Place] = { output =>
    outAdjacent.keys.map { place =>
      val value: Any = {
        interaction.eventsToFire.find(_.name == output.name).map(_.name).getOrElse {
          throw new IllegalStateException(
            s"Method output: $output is not an instance of any of the specified events: ${
              interaction.eventsToFire
                .mkString(",")
            }")
        }
      }
      place -> MultiSet.copyOff(Seq(value))
    }.toMarking
  }
}
