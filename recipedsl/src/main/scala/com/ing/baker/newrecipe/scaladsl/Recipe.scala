package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common

/**
  * A Recipe combines a set of interactions & events.
  */
case class Recipe private (override val name: String,
                           override val interactions: Seq[Interaction],
                           override val sieves: Seq[Interaction],
                           override val events: Set[common.Event])
  extends common.Recipe {

  def withInteraction(newInteraction: Interaction) = copy(interactions = interactions :+ newInteraction)
  def withInteractions(newInteractions: Interaction*) = copy(interactions = interactions ++ newInteractions)

  def withSieve(newSieve: Interaction) = copy(sieves = sieves :+ newSieve)
  def withSieves(newSieves: Interaction*) = copy(sieves = sieves ++ newSieves)

  def withSensoryEvent(newEvent: Event) = copy(events = events + newEvent)
  def withSensoryEvents(newEvents: Event*) = copy(events = events ++ newEvents)

}

object Recipe{
  def apply(name: String): Recipe = {
    Recipe(name, Seq.empty, Seq.empty, Set.empty)
  }
}
