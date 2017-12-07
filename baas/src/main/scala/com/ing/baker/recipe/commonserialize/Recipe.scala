package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

import scala.concurrent.duration.{Duration, FiniteDuration}

case class Recipe private(override val name: String,
                          override val interactions: Seq[common.InteractionDescriptor],
                          override val sieves: Seq[common.InteractionDescriptor],
                          override val sensoryEvents: Set[common.Event],
                          override val defaultFailureStrategy: InteractionFailureStrategy,
                          override val eventReceivePeriod: Option[FiniteDuration],
                          override val retentionPeriod: Option[FiniteDuration])
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
    * This is the same as equals but does not checks if they represent the same recipe
    *
    * @param that
    * @return
    */
  def same(that: common.Recipe): Boolean = {
    if (!that.isInstanceOf[common.Recipe])
      return false
    val other: common.Recipe = that.asInstanceOf[common.Recipe]
    this.name == other.name &&
      this.interactions == other.interactions &&
      this.sieves == other.sieves &&
      this.sensoryEvents == other.sensoryEvents
      this.defaultFailureStrategy == other.defaultFailureStrategy &&
      this.eventReceivePeriod == other.eventReceivePeriod &&
      this.retentionPeriod == other.retentionPeriod
  }

  /**
    * Compares to the other object with just the field gotten from the common.Recipe
    *
    * @param that
    * @return
    */
  @Override
  override def equals(that: scala.Any): Boolean = {
    if (!that.isInstanceOf[common.Recipe])
      return false
    val other: common.Recipe = that.asInstanceOf[common.Recipe]
    this.name == other.name &&
      this.interactions == other.interactions &&
      this.sieves == other.sieves &&
      this.sensoryEvents == other.sensoryEvents &&
      this.defaultFailureStrategy == other.defaultFailureStrategy &&
      this.eventReceivePeriod == other.eventReceivePeriod &&
      this.retentionPeriod == other.retentionPeriod
  }
}
