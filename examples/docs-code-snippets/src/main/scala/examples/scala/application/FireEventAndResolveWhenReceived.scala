package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import examples.scala.events.OrderPlaced

class FireEventAndResolveWhenReceived(val baker: Baker) {

  def example(recipeInstanceId: String, orderPlaced: OrderPlaced): Unit = {
    val eventInstance = EventInstance.unsafeFrom(orderPlaced)
    val sensoryEventStatus = baker.fireEventAndResolveWhenReceived(recipeInstanceId, eventInstance)
  }
}
