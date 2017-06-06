package com.ing.baker.recipe

package object scaladsl {
  implicit def InteractionToInteractionDescriptor(interaction: Interaction): InteractionDescriptor = InteractionDescriptorFactory(interaction)

  implicit def IngredientToIngredientSeq(ingredient: Ingredient[_]): Seq[Ingredient[_]] = Seq(ingredient)

  implicit def StringToRecipe(name: String): Recipe = Recipe(name)
}
