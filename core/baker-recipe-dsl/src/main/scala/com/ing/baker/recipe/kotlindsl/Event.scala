package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.types.Converters

import scala.collection.compat.immutable.ArraySeq

import scala.jdk.CollectionConverters._
import scala.collection.immutable.Seq

class Event(
  nameInput: String,
  ingredientsInput: java.util.List[Ingredient],
  maxFiringLimitInput: java.util.Optional[java.lang.Integer]
) extends common.Event {
  override val name: String = nameInput
  override val providedIngredients: Seq[common.Ingredient] = new ArraySeq.ofRef(ingredientsInput.asScala.toArray)
  override val maxFiringLimit: Option[Int] = maxFiringLimitInput.map[Option[Int]](x => Option.apply(x)).orElse(Option.empty)
}
