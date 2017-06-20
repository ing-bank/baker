package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

/**
  * A Recipe combines a set of interactions & events.
  */
case class Recipe private (override val name: String,
                           override val interactions: Seq[InteractionDescriptor],
                           override val sieves: Seq[InteractionDescriptor],
                           override val sensoryEvents: Set[common.Event],
                           override val defaultFailureStrategy: InteractionFailureStrategy)
  extends common.Recipe {

  def withInteraction(newInteraction: InteractionDescriptor) = copy(interactions = interactions :+ newInteraction)
  def withInteractions(newInteractions: InteractionDescriptor*) = copy(interactions = interactions ++ newInteractions)

  def withSieve(newSieve: InteractionDescriptor) = copy(sieves = sieves :+ newSieve)
  def withSieves(newSieves: InteractionDescriptor*) = copy(sieves = sieves ++ newSieves)

  def withSensoryEvent(newEvent: Event) = copy(sensoryEvents = sensoryEvents + newEvent)
  def withSensoryEvents(newEvents: Event*) = copy(sensoryEvents = sensoryEvents ++ newEvents)
}

object Recipe{
  def apply(name: String): Recipe = {
    Recipe(name, Seq.empty, Seq.empty, Set.empty, InteractionFailureStrategy.BlockInteraction)
  }
}
