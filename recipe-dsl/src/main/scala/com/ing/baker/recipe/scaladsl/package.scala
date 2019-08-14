package com.ing.baker.recipe

package object scaladsl {

  val recipeInstanceId: Ingredient[String] = new Ingredient[String](common.recipeInstanceIdName)
}


