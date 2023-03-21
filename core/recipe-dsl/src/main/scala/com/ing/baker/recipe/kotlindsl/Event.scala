package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.types.Converters

import scala.jdk.CollectionConverters._

class Event(
  nameInput: String,
  ingredientsInput: java.util.List[Ingredient],
  maxFiringLimitInput: java.util.Optional[java.lang.Integer]
) extends common.Event {
  override val name: String = nameInput
  override val providedIngredients: Seq[common.Ingredient] = ingredientsInput.asScala.toSeq
    .map(i => new common.Ingredient(i.name, Converters.readJavaType(i.ingredientType)))
  override val maxFiringLimit: Option[Int] = Option.apply(maxFiringLimitInput.orElse(null))
}
