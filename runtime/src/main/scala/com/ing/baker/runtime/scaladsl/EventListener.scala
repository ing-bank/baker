package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi

trait EventListener extends common.EventListener with ScalaApi {

  type RuntimeEventType = RuntimeEvent

  override def processEvent(processId: String, event: RuntimeEvent) : Unit
}