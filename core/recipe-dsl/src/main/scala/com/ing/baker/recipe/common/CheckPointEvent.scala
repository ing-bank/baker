package com.ing.baker.recipe.common

import com.ing.baker.recipe.common
import com.ing.baker.recipe.scaladsl.Interaction


trait CheckPointEvent {

  /**
   * name of the result event
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
