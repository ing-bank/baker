package com.ing.baker.runtime.akka

import com.ing.baker.runtime.scaladsl.EventInstance
import org.mockito.ArgumentMatcher

class RuntimeEventMatcher(val left: EventInstance) extends ArgumentMatcher[EventInstance] {
  override def matches(right: Any): Boolean = {
    right match {
      case casted: EventInstance =>
        casted.name.equals(left.name) &&
          casted.providedIngredients.equals(left.providedIngredients)
      case _ => false
    }
  }
}
