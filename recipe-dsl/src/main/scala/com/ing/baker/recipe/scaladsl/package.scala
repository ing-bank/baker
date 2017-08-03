package com.ing.baker.recipe

package object scaladsl {
  implicit def InteractionToInteractionDescriptor(interaction: Interaction): InteractionDescriptor = InteractionDescriptorFactory(interaction)

  implicit def InteractionToInteractionDescriptorWithRename(interactionNameTuple:(Interaction, String)): InteractionDescriptor = InteractionDescriptorFactory(interactionNameTuple._1, interactionNameTuple._2)


  implicit def IngredientToIngredientSeq(ingredient: Ingredient[_]): Seq[Ingredient[_]] = Seq(ingredient)

  implicit def StringToRecipe(name: String): Recipe = Recipe(name)

  val processId: Ingredient[_] = new Ingredient[String](common.ProcessIdName)

  object Ingredients {
    def apply(ingredients: Ingredient[_]*): Seq[Ingredient[_]] = ingredients.toSeq
  }
}


