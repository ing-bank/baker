package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import examples.scala.events.OrderPlaced

class FireEvent(val baker: Baker) {

  def example(recipeInstanceId: String): Unit = {
    val eventInstance = EventInstance.unsafeFrom(OrderPlaced.event)

    val eventResolutions = baker.fireEvent(recipeInstanceId, eventInstance)
    val sensoryEventStatus = eventResolutions.resolveWhenReceived
    val sensoryEventResult = eventResolutions.resolveWhenCompleted
  }
}
