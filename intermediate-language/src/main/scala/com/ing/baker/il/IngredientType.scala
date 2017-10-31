package com.ing.baker.il

import java.lang.reflect.Type

sealed trait IngredientType

//Direct ingredients
case class BaseType(javaType: Type) extends IngredientType

case class ListType(entryType: IngredientType) extends IngredientType

case class OptionType(entryType: IngredientType) extends IngredientType

case class EnumType(options: Set[String]) extends IngredientType

//POJO ingredient
case class POJOType(fields: Seq[IngredientDescriptor]) extends IngredientType

