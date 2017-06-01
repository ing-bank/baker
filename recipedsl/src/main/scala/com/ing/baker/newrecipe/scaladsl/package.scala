package com.ing.baker.newrecipe

package object scaladsl {
  implicit def InteractionToInteractionDescriptor(interaction: Interaction): InteractionDescriptor = InteractionDescriptorFactory(interaction)

//  implicit def InteractionToInteractionSeq(interaction: Interaction): Seq[Interaction] = Seq(interaction)

  implicit def IngredientToIngredientSeq(ingredient: Ingredient[_]): Seq[Ingredient[_]] = Seq(ingredient)

//  implicit def EventToEventSeq(event: Event): Seq[Event] = Seq(event)
}
