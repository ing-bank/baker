package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

trait IngredientInstance extends LanguageApi {

  val name: String

  val value: Value
}
