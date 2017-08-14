package com.ing.baker.runtime

import com.ing.baker.il.petrinet.{FiresOneOfEvents, InteractionTransition, Place}
import com.ing.baker.petrinet.api.{Marking, MultiSet}
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.petrinet.api._

package object petrinet {
  /**
    * Creates the produced marking (tokens) given the output (event) of the interaction.
    */
  def createProducedMarking[A](interaction: InteractionTransition[A], outAdjacent: MultiSet[Place[_]]): RuntimeEvent => Marking[Place] = { output =>
    outAdjacent.keys.map { place =>
      val value: Any = {
        interaction.providesType match {
          case FiresOneOfEvents(events, _) =>
            events.find(_.name == output.name).map(_.name).getOrElse {
              throw new IllegalStateException(
                s"Method output: $output is not an instance of any of the specified events: ${
                  events
                    .mkString(",")
                }")
            }
          case _ => ()
        }
      }
      place -> MultiSet.copyOff(Seq(value))
    }.toMarking
  }

}
