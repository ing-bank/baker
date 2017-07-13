package com.ing.baker.runtime.core

/**
  * Listener interface for events from baker.
  */
trait EventListener {

  /**
    * Called when an event occured.
    *
    * @param processId The process id for which the event occured.
    * @param event The event.
    */
  def processEvent(processId: String, event: RuntimeEvent)
}
