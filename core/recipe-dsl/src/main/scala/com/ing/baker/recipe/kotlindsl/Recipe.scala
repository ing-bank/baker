package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common

import java.util.concurrent.TimeUnit
import scala.collection.compat.immutable.ArraySeq
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
  retentionPeriodInput: java.util.Optional[java.time.Duration],
  checkpointEventsInput: java.util.Set[CheckPointEvent]
) extends common.Recipe {

  override val name: String = nameInput
  override val interactions: Seq[Interaction] = new ArraySeq.ofRef(interactionsInput.asScala.toArray)
  override val sensoryEvents: Set[common.Event] = sensoryEventsInput.asScala.toSet
  override val defaultFailureStrategy: common.InteractionFailureStrategy = defaultFailureStrategyInput
  override val eventReceivePeriod: Option[FiniteDuration] = eventReceivePeriodInput.map[Option[FiniteDuration]](d => Option.apply(FiniteDuration(d.toNanos, TimeUnit.NANOSECONDS))).orElse(None)
  override val retentionPeriod: Option[FiniteDuration] = retentionPeriodInput.map[Option[FiniteDuration]](d => Option.apply(FiniteDuration(d.toNanos, TimeUnit.NANOSECONDS))).orElse(None)
  override val checkpointEvents: Set[common.CheckPointEvent] = checkpointEventsInput.asScala.toSet
}
