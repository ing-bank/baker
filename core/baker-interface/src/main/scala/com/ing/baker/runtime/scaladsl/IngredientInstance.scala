package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.types.Value

case class IngredientInstance(name: String, value: Value) extends common.IngredientInstance with ScalaApi {

  def asJava: javadsl.IngredientInstance = javadsl.IngredientInstance(name, value)
}

