package com.ing.baker.il

import com.ing.baker.il.petrinet.HasCustomToStringForRecipeId

import scala.collection.immutable.Seq
/**
  * Describes an event.
  *
  * @param name The name of an event.
  * @param ingredients The ingredients the event produces.
  */
case class EventDescriptor(name: String,
                           ingredients: Seq[IngredientDescriptor]) extends HasCustomToStringForRecipeId {

  // Used in CompiledRecipe to generate the hash. This is a workaround to keep the hash the same.
  // This method mimics the result of toString before ingredients was of type scala.collection.immutable.Seq[IngredientDescriptor].
  override def toStringForRecipeId(recipeIdVariant: CompiledRecipe.RecipeIdVariant): String =
    s"EventDescriptor($name,${ingredients.toRecipeIdStringTypeB(recipeIdVariant)})"

}