package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

class EventListener(consumer: java.util.function.BiConsumer[String, RuntimeEvent]) extends common.EventListener with JavaApi {

  type RuntimeEventType = RuntimeEvent

  override def processEvent(processId: String, event: RuntimeEvent): Unit = consumer.accept(processId, event)
}
