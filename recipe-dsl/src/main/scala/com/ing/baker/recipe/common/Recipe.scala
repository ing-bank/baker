package com.ing.baker.recipe.common

import scala.concurrent.duration.Duration

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
    * The set of sieves.
    */
  val sieves: Seq[InteractionDescriptor]

  /**
    * The set of events.
    */
  val sensoryEvents: Set[Event]

  val defaultFailureStrategy: InteractionFailureStrategy

  /**
    * The period that processes can receive events for this recipe.
    */
  val eventReceivePeriod: Duration
}
