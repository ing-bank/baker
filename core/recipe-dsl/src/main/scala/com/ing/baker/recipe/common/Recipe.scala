package com.ing.baker.recipe.common

import scala.concurrent.duration.FiniteDuration

/**
  * A Recipe combines a set of interactions & events.
  */
trait Recipe {

  /**
    * The name of the recipe.
    */
  val name: String

  /**
    * The set of interactions.
    */
  val interactions: Seq[InteractionDescriptor]

  /**
    * The set of events.
    */
  val sensoryEvents: Set[Event]

  /**
    * The default interaction failure strategy.
    */
  val defaultFailureStrategy: InteractionFailureStrategy

  /**
    * The period that processes can receive events for this recipe.
    *
    * If Duration.Undefined, events will always be accepted.
    */
  val eventReceivePeriod: Option[FiniteDuration]

  /**
    * The period that processes are stored.
    *
    * If Duration.Undefined, process data will be stored indefinitely.
    */
  val retentionPeriod: Option[FiniteDuration]
}
