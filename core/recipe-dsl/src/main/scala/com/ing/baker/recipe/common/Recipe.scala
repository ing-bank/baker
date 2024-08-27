package com.ing.baker.recipe.common

import scala.concurrent.duration.FiniteDuration
import scala.collection.immutable.Seq

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
   * The set of interactions.
   */
  val subRecipes: Set[Recipe]

  /**
    * The set of sensory events.
    */
  val sensoryEvents: Set[Event]

  /**
   * The set of checkpoint events.
   */
  val checkpointEvents: Set[CheckPointEvent]

  /**
   * The set of sieves.
   */
  val sieves: Set[Sieve]

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

  /**
   * Returns all interaction inclusive recursively all sub recipes
   */
  def allInteractions: Seq[InteractionDescriptor] = interactions ++ subRecipes.flatMap(_.allInteractions)
}
