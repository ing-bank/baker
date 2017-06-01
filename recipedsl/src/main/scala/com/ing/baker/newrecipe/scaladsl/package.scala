package com.ing.baker.newrecipe

package object scaladsl {
  implicit def InteractionToInteractionDescriptor(interaction: Interaction): InteractionDescriptor = InteractionDescriptorFactory(interaction)

  implicit def IngredientToIngredientSeq(ingredient: Ingredient[_]): Seq[Ingredient[_]] = Seq(ingredient)
}
