package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.types.Converters

import scala.jdk.CollectionConverters._
import scala.collection.immutable.{List, Seq}

class Event(
  nameInput: String,
  ingredientsInput: java.util.List[Ingredient],
  maxFiringLimitInput: java.util.Optional[java.lang.Integer]
) extends common.Event {
  override val name: String = nameInput
  override val providedIngredients: Seq[common.Ingredient] = List.apply(ingredientsInput.asScala.toSeq:_*)
  override val maxFiringLimit: Option[Int] = maxFiringLimitInput.map[Option[Int]](x => Option.apply(x)).orElse(Option.empty)
}
