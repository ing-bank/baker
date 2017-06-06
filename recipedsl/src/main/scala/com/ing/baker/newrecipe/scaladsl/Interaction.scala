package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common
import com.ing.baker.newrecipe.common._

case class Interaction(override val name: String,
                       override val inputIngredients: Seq[Ingredient[_]],
                       override val output: InteractionOutput)
  extends common.Interaction
