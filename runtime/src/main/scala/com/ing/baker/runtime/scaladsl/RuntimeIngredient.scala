package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.types.Value

case class RuntimeIngredient(name: String, value: Value) extends common.RuntimeIngredient with ScalaApi {

  def asJava: javadsl.RuntimeIngredient = new javadsl.RuntimeIngredient(name, value)
}

