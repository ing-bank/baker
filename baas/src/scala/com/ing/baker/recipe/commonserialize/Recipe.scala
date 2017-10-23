package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

import scala.concurrent.duration.Duration

case class Recipe private(override val name: String,
                          override val interactions: Seq[common.InteractionDescriptor],
                          override val sieves: Seq[common.InteractionDescriptor],
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
      recipe.retentionPeriod)

  /**
    * Compares to the other object with just the field gotten from the common.Recipe
    *
    * @param obj
    * @return
    */
  override def equals(obj: scala.Any): Boolean = {
    if (!obj.isInstanceOf[common.Recipe])
      return false
    val other: common.Recipe = obj.asInstanceOf[common.Recipe]
    this.name == other.name &&
      this.interactions == other.interactions &&
      this.sieves == other.sieves &&
      this.sensoryEvents == other.sensoryEvents &&
      this.defaultFailureStrategy == other.defaultFailureStrategy &&
      equalsOnDuration(this.eventReceivePeriod, other.eventReceivePeriod) &&
      equalsOnDuration(this.retentionPeriod, other.retentionPeriod)
  }

  def equalsOnDuration(original: Duration, other: Duration): Boolean = {
    (original, other) match {
      case (x, y) if !x.isFinite() && !y.isFinite() => true
      case (x, y) => x == y
    }
  }
}
