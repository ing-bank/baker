package com.ing.baker.runtime.model.recipeinstance

import java.time.Duration
import java.util.Optional

case class RecipeInstanceConfig(
                                 idleTTL: Optional[Duration] = Optional.of(Duration.ofSeconds(5)),
                                 ingredientsFilter: java.util.List[String] = java.util.List.of()
                               ) {

  def withIdleTTL(idleTTL: Optional[Duration]) = copy(idleTTL = idleTTL)

  def withIngredientsFilter(ingredientsFilter: java.util.List[String]) =
    copy(ingredientsFilter = ingredientsFilter)
}