package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

case class Ingredient[T : scala.reflect.runtime.universe.TypeTag](override val name: String) extends common.Ingredient(name, common.ingredientTypeFromType(common.makeType[T]))

