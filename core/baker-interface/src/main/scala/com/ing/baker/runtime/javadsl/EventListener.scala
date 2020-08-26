package com.ing.baker.runtime.javadsl

/**
  * Listener interface for events from baker.
  */
@Deprecated
trait EventListener {

  /**
    * Called when an event occurred.
    *
    * @param recipeInstanceId The process id for which the event occurred.
    *
    * @param event The event.
    */
  def processEvent(recipeInstanceId: String, event: EventInstance)
}
