package com.ing.baker.recipe

import java.util.UUID

package object scaladsl {
  implicit def InteractionToInteractionDescriptor(interaction: Interaction): InteractionDescriptor = InteractionDescriptorFactory(interaction)

  implicit def IngredientToIngredientSeq(ingredient: Ingredient[_]): Seq[Ingredient[_]] = Seq(ingredient)

  implicit def StringToRecipe(name: String): Recipe = Recipe(name)

  val processId: Ingredient[_] = new Ingredient[String](common.ProcessIdName)
  val processIdUUID: Ingredient[_] = new Ingredient[UUID](common.ProcessIdName)

  object Ingredients {
    def apply(ingredients: Ingredient[_]*): Seq[Ingredient[_]] = ingredients.toSeq
  }
}


