package com.ing.baker.baas.common

import com.ing.baker.runtime.common.BakerEvent
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait RemoteBakerEventListener[F[_]] extends LanguageApi { self =>

  type BakerEventType <: BakerEvent { type Language <: self.Language }

  def load(listenerFunction: language.ConsumerFunction[BakerEventType]): Unit

}
