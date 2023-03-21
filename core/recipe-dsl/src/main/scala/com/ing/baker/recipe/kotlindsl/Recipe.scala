package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common

import scala.concurrent.duration.FiniteDuration
import scala.jdk.CollectionConverters._

import scala.collection.immutable.Seq
import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

class Recipe(
  nameInput: String,
  interactionsInput: java.util.List[Interaction],
  sensoryEventsInput: java.util.List[Event],
  defaultFailureStrategyInput: common.InteractionFailureStrategy,
  eventReceivePeriodInput: java.util.Optional[java.time.Duration],
  retentionPeriodInput: java.util.Optional[java.time.Duration]
) extends common.Recipe {

  override val name: String = nameInput
  override val interactions: Seq[Interaction] = List.apply(interactionsInput.asScala.toSeq:_*)
  override val sensoryEvents: Set[common.Event] = sensoryEventsInput.asScala.toSet
  override val defaultFailureStrategy: common.InteractionFailureStrategy = defaultFailureStrategyInput
  override val eventReceivePeriod: Option[FiniteDuration] = None //eventReceivePeriodInput
  override val retentionPeriod: Option[FiniteDuration] = None //retentionPeriodInput
}
