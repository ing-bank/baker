package com.ing.baker.runtime.core

trait EventListener {

  def processEvent(processId: String, event: RuntimeEvent)
}
