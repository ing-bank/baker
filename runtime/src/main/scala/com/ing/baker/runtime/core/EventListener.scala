package com.ing.baker.runtime.core

/**
  * Listener interface for events from baker.
  */
//@deprecated("Use event bus instead", "1.4.0")
trait EventListener {

  /**
    * Called when an event occurred.
    *
    * @param processId The process id for which the event occurred.
    *
    * @param event The event.
    */
  def processEvent(processId: String, event: RuntimeEvent)
}
