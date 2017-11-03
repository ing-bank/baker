package com.ing.baker.recipe.common

sealed trait IngredientType

//Direct ingredients
case class PrimitiveType(clazz: Class[_]) extends IngredientType

case class ListType(entryType: IngredientType) extends IngredientType

case class OptionType(entryType: IngredientType) extends IngredientType

case class EnumType(options: Set[String]) extends IngredientType

//POJO ingredient
case class POJOType(fields: Seq[Ingredient]) extends IngredientType

