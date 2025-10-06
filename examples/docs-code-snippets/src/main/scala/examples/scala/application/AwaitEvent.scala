package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import examples.scala.events.OrderPlaced

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.DurationInt

class AwaitEvent(val baker: Baker) {

  def example(recipeInstanceId: String, orderPlaced: OrderPlaced): Unit = {
    val eventInstance = EventInstance.unsafeFrom(orderPlaced)
    for {
      _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, eventInstance)
      _ <- baker.awaitEvent(recipeInstanceId, "ExpectedEvent", timeout = 5.seconds)
    } yield ()
  }
}
