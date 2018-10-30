package com.ing.baker.runtime.core.implementations

import com.ing.baker.recipe.TestRecipe
import com.ing.baker.recipe.TestRecipe.InteractionOneSuccessful

class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
  override def apply(processId: String, initialIngredient: String): InteractionOneSuccessful = InteractionOneSuccessful("")
}
