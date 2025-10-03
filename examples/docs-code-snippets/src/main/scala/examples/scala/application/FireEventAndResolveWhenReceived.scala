package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import examples.scala.events.OrderPlaced

import scala.concurrent.ExecutionContext.Implicits.global

class FireEventAndResolveWhenReceived(val baker: Baker) {

  def example(recipeInstanceId: String, orderPlaced: OrderPlaced): Unit = {
    val eventInstance = EventInstance.unsafeFrom(orderPlaced)
    for {
      _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, eventInstance)
    } yield ()
  }
}
