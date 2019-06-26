package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

/**
  * Listener interface for events from baker.
  */
trait EventListener extends LanguageApi { self =>

  type RuntimeEventType <: RuntimeEvent { type Language = self.Language }

  /**
    * Called when an event occurred.
    *
    * @param processId The process id for which the event occurred.
    *
    * @param event The event.
    */
  def processEvent(processId: String, event: RuntimeEventType): Unit
}
