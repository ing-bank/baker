package com.ing.baker.runtime.common

import com.ing.baker.runtime.scaladsl

/**
  * Listener interface for events from baker.
  */
trait EventListener {

  /**
    * Called when an event occurred.
    *
    * @param processId The process id for which the event occurred.
    *
    * @param event The event.
    */
  // TODO refactor EventLsitener to use correct RuntimeEvent
  def processEvent(processId: String, event: scaladsl.RuntimeEvent)
}
