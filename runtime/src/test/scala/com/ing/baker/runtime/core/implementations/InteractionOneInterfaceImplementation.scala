package com.ing.baker.runtime.core.implementations

import com.ing.baker.recipe.TestRecipe
import com.ing.baker.recipe.TestRecipe.InteractionOneSuccessful

import scala.concurrent.Future

class InteractionOneInterfaceImplementation() extends TestRecipe.InteractionOne {
  override def apply(processId: String, initialIngredient: String): Future[InteractionOneSuccessful] = Future.successful(InteractionOneSuccessful(""))
}
