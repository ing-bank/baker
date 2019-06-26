package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait EventMoment extends LanguageApi {

  def name: String

  def occurredOn: Long
}
