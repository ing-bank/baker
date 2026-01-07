package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import examples.scala.events.OrderPlaced

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.DurationInt

class AwaitEventWaitForNext(val baker: Baker) {

  def example(recipeInstanceId: String, orderPlaced: OrderPlaced): Unit = {
    val eventInstance = EventInstance.unsafeFrom(orderPlaced)
    
    // Pattern: Start waiting BEFORE firing the sensory event
    // waitForNext = true checks for *new* occurrences of the event
    val awaitFuture = baker.awaitEvent(recipeInstanceId, "ExpectedEvent", timeout = 5.seconds, waitForNext = true)
    
    // Fire the event
    // We combine the futures to ensure we wait for both:
    // 1. The event to be received
    // 2. The expected event to occur
    val result = for {
      _ <- baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, eventInstance)
      _ <- awaitFuture 
    } yield ()
  }
}
