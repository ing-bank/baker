package com.ing.baker.recipe.common

trait CheckPointEvent {

  /**
   * name of the checkpoint event
   */
  val name: String

  /**
   * A set of names of the events AND preconditions (events)
   */
  val requiredEvents: Set[String]

  /**
   * A set of names of the events OR preconditions (events)
   */
  val requiredOneOfEvents: Set[Set[String]]

}
