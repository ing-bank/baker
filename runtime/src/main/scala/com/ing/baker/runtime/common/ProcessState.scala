package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

/**
  * Holds the 'state' of a process instance.
  */
trait ProcessState extends LanguageApi {

  def processId: String

  def ingredients: language.Map[String, Value]

  def eventNames: language.Seq[String]
}
