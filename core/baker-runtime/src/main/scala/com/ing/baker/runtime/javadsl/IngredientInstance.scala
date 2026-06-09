package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value

case class IngredientInstance(name: String, value: Value) extends common.IngredientInstance with JavaApi {

  def getName: String = name

  def getValue: Value = value

  def asScala: scaladsl.IngredientInstance = scaladsl.IngredientInstance(name, value)
}
