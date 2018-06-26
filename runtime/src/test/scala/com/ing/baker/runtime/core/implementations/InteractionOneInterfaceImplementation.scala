package com.ing.baker.runtime.core.implementations

import com.ing.baker.recipe.TestRecipe

class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
  override def apply(processId: String, initialIngredient: String): String = ""
}
