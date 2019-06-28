package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

class IngredientInstance(val name: String, val value: Value) extends common.IngredientInstance with JavaApi {

  def asScala: scaladsl.IngredientInstance = scaladsl.IngredientInstance(name, value)
}
