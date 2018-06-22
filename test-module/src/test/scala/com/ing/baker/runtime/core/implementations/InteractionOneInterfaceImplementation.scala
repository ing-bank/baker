package com.ing.baker.runtime.core.implementations

import com.ing.baker.TestRecipe

class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
  override def apply(processId: String, initialIngredient: String): String = ""
}
