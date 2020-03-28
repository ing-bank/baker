package com.ing.baker.baas.mocks

import cats.effect.IO
import com.ing.baker.runtime.akka.EventSink
import com.ing.baker.runtime.common.{BakerEvent, EventInstance}
import com.ing.baker.runtime.scaladsl.RecipeEventMetadata

import scala.collection.mutable

class EventListener {

  val events: mutable.ListBuffer[String] = mutable.ListBuffer.empty[String]

  val eventSink: EventSink = new EventSink() {
    def fire(event: Any): Unit = {
      event match {
        case _: BakerEvent =>
        case _: EventInstance | _: RecipeEventMetadata =>
          events.append(event.toString)
      }
    }
    def lastEvents: Seq[String] = events.map(_.toString)
  }

  def verifyEventsReceived(times: Int): IO[Unit] = IO {
    assert(events.size == times, s"Expected $times messages, got ${events.size}")
    events.clear()
  }

  def verifyNoEventsArrived: IO[Unit] = IO {
    events.clear()
  }
}
