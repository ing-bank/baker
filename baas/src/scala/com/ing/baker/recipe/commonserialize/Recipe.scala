package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

import scala.concurrent.duration.Duration

case class Recipe private(override val name: String,
                          override val interactions: Seq[InteractionDescriptor],
                          override val sieves: Seq[InteractionDescriptor],
                          override val sensoryEvents: Set[common.Event],
                          override val defaultFailureStrategy: InteractionFailureStrategy,
                          override val eventReceivePeriod: Duration,
                          override val retentionPeriod: Duration)
  extends common.Recipe {

  def this(recipe: common.Recipe) =
    this(
      recipe.name,
      recipe.interactions.map(i => new InteractionDescriptor(i)),
      recipe.sieves.map(s => new InteractionDescriptor(s)),
      recipe.sensoryEvents.map(e => new Event(e)),
      recipe.defaultFailureStrategy,
      recipe.eventReceivePeriod,
      recipe.eventReceivePeriod)
}
