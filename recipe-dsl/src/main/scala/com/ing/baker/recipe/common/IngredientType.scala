package com.ing.baker.recipe.common

import java.lang.reflect.Type

sealed trait IngredientType

case class BaseType(javaType: Type) extends IngredientType

case class ListType(entryType: IngredientType) extends IngredientType

case class OptionType(entryType: IngredientType) extends IngredientType

case class RecordType(fields: Seq[Ingredient]) extends IngredientType

case class EnumType(options: Set[String]) extends IngredientType

