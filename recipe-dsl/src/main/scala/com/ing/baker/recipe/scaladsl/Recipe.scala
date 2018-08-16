package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

import scala.concurrent.duration.FiniteDuration
import scala.language.experimental.macros

object Recipe {
  def apply() : Recipe = macro CommonMacros.recipeImpl

  def apply(name: String): Recipe = {
    Recipe(name, Seq.empty, Seq.empty, Set.empty, new common.InteractionFailureStrategy.BlockInteraction, None, None)
  }
}

/**
  * A Recipe combines a set of interactions & events.
  */
case class Recipe private(override val name: String,
                          override val interactions: Seq[Interaction],
                          override val sieves: Seq[Interaction],
                          override val sensoryEvents: Set[common.Event],
                          override val defaultFailureStrategy: InteractionFailureStrategy,
                          override val eventReceivePeriod: Option[FiniteDuration],
                          override val retentionPeriod: Option[FiniteDuration])
  extends common.Recipe {

  def withInteraction(newInteraction: Interaction): Recipe = copy(interactions = interactions :+ newInteraction)

  def withInteractions(newInteractions: Interaction*): Recipe = copy(interactions = interactions ++ newInteractions)

  @deprecated("sieves are deprecated, use interactions instead", "1.4.0")
  def withSieve(newSieve: Interaction): Recipe = copy(sieves = sieves :+ newSieve)

  @deprecated("sieves are deprecated, use interactions instead", "1.4.0")
  def withSieves(newSieves: Interaction*): Recipe = copy(sieves = sieves ++ newSieves)

  def withSensoryEvent(newEvent: Event): Recipe = copy(sensoryEvents = sensoryEvents + newEvent)

  def withSensoryEvents(newEvents: Event*): Recipe = copy(sensoryEvents = sensoryEvents ++ newEvents)

  def withEventReceivePeriod(duration: FiniteDuration): Recipe = copy(eventReceivePeriod = Some(duration))

  def withRetentionPeriod(duration: FiniteDuration): Recipe = copy(retentionPeriod = Some(duration))
}