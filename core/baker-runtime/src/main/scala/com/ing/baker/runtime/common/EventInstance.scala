package com.ing.baker.runtime.common

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

trait EventInstance extends LanguageApi {

  def name: String

  def providedIngredients: language.Map[String, Value]

  def validate(descriptor: EventDescriptor): language.Seq[String]
}
