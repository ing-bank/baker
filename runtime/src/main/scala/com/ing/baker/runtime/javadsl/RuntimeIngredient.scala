package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

class RuntimeIngredient(val name: String, val value: Value) extends common.RuntimeIngredient with JavaApi {

  def asScala: scaladsl.RuntimeIngredient = scaladsl.RuntimeIngredient(name, value)
}
