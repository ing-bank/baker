package com.ing.baker.runtime.event_extractors
import com.ing.baker.runtime.core.RuntimeEvent

class MapEventExtractor extends EventExtractor {

  // This is the reserved key to extract the event name.
  val eventNameKey = "$EventName$"

  /**
    * Extracts the ingredient data from a given object.
    *
    * @param obj The object.
    * @return The ingredient data.
    */
  override def extractEvent(obj: Any): RuntimeEvent = {

    obj match {
      case map: Map[_, _] =>
        val values = map.asInstanceOf[Map[String, Any]]
        val eventName = values(eventNameKey).asInstanceOf[String]
        val ingredients = (values - eventNameKey).toSeq
        RuntimeEvent(eventName, ingredients)

      case _ => throw new IllegalArgumentException(s"Cannot translate object into RuntimeEvent: $obj")
    }
  }
}
