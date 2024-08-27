package com.ing.baker.recipe.common

import com.ing.baker.recipe.common

trait Sieve {

  /**
   * name of the sieve interaction
   */
  val name: String

  /**
   * input ingredients
   */
  val inputIngredients: Seq[common.Ingredient]

  /**
   * output events
   */
  val output: Seq[common.Event]

  /**
   * function
   */
  val function: Any

}
