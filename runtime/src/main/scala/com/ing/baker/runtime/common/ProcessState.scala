package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

/**
  * Holds the 'state' of a process instance.
  */
trait ProcessState extends LanguageApi { self =>

  type EventType <: RuntimeEvent { type Language <: self.Language}

  def processId: String

  def ingredients: language.Map[String, Value]

  def events: language.Seq[EventType]
}
