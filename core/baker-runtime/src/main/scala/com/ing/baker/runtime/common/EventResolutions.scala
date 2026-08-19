package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait EventResolutions[F[_]] extends LanguageApi { self =>

  type SensoryEventResultType <: SensoryEventResult { type Language <: self.Language}

  def resolveWhenReceived: F[SensoryEventStatus]

  def resolveWhenCompleted: F[SensoryEventResultType]
}
