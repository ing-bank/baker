package com.ing.baker.newrecipe.common

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
  val events: Set[Event]
}
