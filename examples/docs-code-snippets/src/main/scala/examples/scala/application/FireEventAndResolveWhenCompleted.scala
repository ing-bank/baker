package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import examples.scala.events.OrderPlaced

class FireEventAndResolveWhenCompleted(val baker: Baker) {

  def example(recipeInstanceId: String, orderPlaced: OrderPlaced): Unit = {
    val eventInstance = EventInstance.unsafeFrom(orderPlaced)
    val sensoryEventResult = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, eventInstance)
  }
}
