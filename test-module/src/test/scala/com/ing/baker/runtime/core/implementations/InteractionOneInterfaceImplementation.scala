package com.ing.baker.runtime.core.implementations

import com.ing.baker.TestRecipeHelper

class InteractionOneInterfaceImplementation() extends TestRecipeHelper.InteractionOne {
  override def apply(processId: String, initialIngredient: String): String = ""
}
