package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.{common, javadsl}

import scala.concurrent.duration.FiniteDuration

import scala.jdk.CollectionConverters._

case class Recipe(
  nameInput: String,
  interactionsInput: java.util.List[Interaction],
  sensoryEventsInput: java.util.List[Class[_]],
  defaultFailureStrategyInput: common.InteractionFailureStrategy,
  eventReceivePeriodInput: java.util.Optional[FiniteDuration],
  retentionPeriodInput: java.util.Optional[FiniteDuration]
) extends common.Recipe {

  def eventClassToCommonEvent(eventClass: Class[_], firingLimit: Option[Int]): common.Event = new javadsl.Event(eventClass, firingLimit)

  override val name = nameInput
  override val interactions = interactionsInput.asScala.toSeq
  override val sensoryEvents = sensoryEventsInput.asScala.map(eventClassToCommonEvent(_, Some(1))).toSet
  override val defaultFailureStrategy = defaultFailureStrategyInput
  override val eventReceivePeriod = None //eventReceivePeriodInput
  override val retentionPeriod = None //retentionPeriodInput
}

