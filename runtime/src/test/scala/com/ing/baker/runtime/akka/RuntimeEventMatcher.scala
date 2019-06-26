package com.ing.baker.runtime.akka

import com.ing.baker.runtime.scaladsl.RuntimeEvent
import org.mockito.ArgumentMatcher

class RuntimeEventMatcher(val left: RuntimeEvent) extends ArgumentMatcher[RuntimeEvent] {
  override def matches(right: Any): Boolean = {
    right match {
      case casted: RuntimeEvent =>
        casted.name.equals(left.name) &&
          casted.providedIngredients.equals(left.providedIngredients)
      case _ => false
    }
  }
}
