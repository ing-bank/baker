package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

import scala.language.experimental.macros

import scala.concurrent.duration.Duration

object Recipe {
  def apply() : Recipe = macro CommonMacros.recipeImpl

  def apply(name: String): Recipe = {
    Recipe(name, Seq.empty, Seq.empty, Set.empty, new common.InteractionFailureStrategy.BlockInteraction, Duration.Undefined, Duration.Undefined)
  }
}

/**
  * A Recipe combines a set of interactions & events.
  */
case class Recipe private(override val name: String,
                          override val interactions: Seq[InteractionDescriptor],
                          override val sieves: Seq[InteractionDescriptor],
                          override val sensoryEvents: Set[common.Event],
                          override val defaultFailureStrategy: InteractionFailureStrategy,
                          override val eventReceivePeriod: Duration,
                          override val retentionPeriod: Duration)
  extends common.Recipe {

  def withInteraction(newInteraction: InteractionDescriptor): Recipe = copy(interactions = interactions :+ newInteraction)

  def withInteractions(newInteractions: InteractionDescriptor*): Recipe = copy(interactions = interactions ++ newInteractions)

  def withSieve(newSieve: InteractionDescriptor): Recipe = copy(sieves = sieves :+ newSieve)

  def withSieves(newSieves: InteractionDescriptor*): Recipe = copy(sieves = sieves ++ newSieves)

  def withSensoryEvent(newEvent: Event): Recipe = copy(sensoryEvents = sensoryEvents + newEvent)

  def withSensoryEvents(newEvents: Event*): Recipe = copy(sensoryEvents = sensoryEvents ++ newEvents)

  def withEventReceivePeriod(duration: Duration): Recipe = copy(eventReceivePeriod = duration)

  def withRetentionPeriod(duration: Duration): Recipe = copy(retentionPeriod = duration)
}