package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common
import com.ing.baker.types.Converters

case class Ingredient[T : scala.reflect.runtime.universe.TypeTag](override val name: String) extends common.Ingredient(name, Converters.readJavaType[T])

