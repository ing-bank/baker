package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait SensoryEventMoments[F[_]] extends LanguageApi { self =>

  type Result <: SensoryEventResult { type Language <: self.Language}

  def received: F[SensoryEventStatus]

  def completed: F[Result]
}


