package com.ing.baker.recipe

package object scaladsl {

  implicit def IngredientToIngredientSeq(ingredient: common.Ingredient): Seq[common.Ingredient] = Seq(ingredient)

  implicit def StringToRecipe(name: String): Recipe = Recipe(name)

  val processId: Ingredient[_] = new Ingredient[String](common.ProcessIdName)
}


