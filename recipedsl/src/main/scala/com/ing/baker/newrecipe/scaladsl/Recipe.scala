package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common

/**
  * A Recipe combines a set of interactions & events.
  */
case class Recipe private (override val name: String,
                           override val interactions: Seq[InteractionDescriptor],
                           override val sieves: Seq[InteractionDescriptor],
                           override val events: Set[common.Event])
  extends common.Recipe {

  def withInteraction(newInteraction: InteractionDescriptor) = copy(interactions = interactions :+ newInteraction)
  def withInteractions(newInteractions: InteractionDescriptor*) = copy(interactions = interactions ++ newInteractions)

  def withSieve(newSieve: InteractionDescriptor) = copy(sieves = sieves :+ newSieve)
  def withSieves(newSieves: InteractionDescriptor*) = copy(sieves = sieves ++ newSieves)

  def withSensoryEvent(newEvent: Event) = copy(events = events + newEvent)
  def withSensoryEvents(newEvents: Event*) = copy(events = events ++ newEvents)

  override def toString: String = {
    s"""
       |  Recipe: $name
       |  Interactions:{
       |${interactions.foldLeft("")((i, j) => s"$i\n${j.toString("    ")}").replaceFirst("\n", "")}
       |  }
       |  Sieves:{
       |${sieves.foldLeft("")((i, j) => s"$i\n${j.toString("    ")}").replaceFirst("\n", "")}
       |  }
       |  Events:{
       |${events.foldLeft("")((i, j) => s"$i\n    $j").replaceFirst("\n", "")}
       |  }
       |""".stripMargin
  }

}

object Recipe{
  def apply(name: String): Recipe = {
    Recipe(name, Seq.empty, Seq.empty, Set.empty)
  }
}
