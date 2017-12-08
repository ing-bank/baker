package com.ing.baker.runtime.event_extractors

import com.ing.baker.types.{Converters, RecordValue}
import com.ing.baker.runtime.core.RuntimeEvent

class PojoEventExtractor extends EventExtractor {

  override def extractEvent(obj: Any): RuntimeEvent = {

    Converters.toValue(obj) match {
      case RecordValue(entries) =>
        val ingredients = entries.toSeq
        RuntimeEvent(obj.getClass.getSimpleName, ingredients)
      case other =>
        throw new IllegalArgumentException(s"Unexpected value: $other")
    }
  }
}