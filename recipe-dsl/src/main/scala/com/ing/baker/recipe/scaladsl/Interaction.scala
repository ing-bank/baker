package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common.InteractionOutput
import com.ing.baker.recipe.common

case class Interaction(override val name: String,
                       override val inputIngredients: Seq[common.Ingredient],
                       override val output: InteractionOutput)
  extends common.Interaction
