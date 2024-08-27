package com.ing.bakery.baker.mocks

import cats.effect.{ContextShift, IO}
import com.ing.baker.runtime.common.{BakerEvent, EventFired, EventInstance}
import com.ing.bakery.components.EventSink

import scala.collection.mutable

class EventListener {

  val events: mutable.ListBuffer[String] = mutable.ListBuffer.empty[String]

  val eventSink: EventSink = new EventSink() {

    def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit] = {
      event match {
        case eventFired: EventFired     =>
          events.append(eventFired.eventName)
        case _: BakerEvent     =>
      }
      IO.unit
    }

  }

  def verifyEventsReceived(times: Int): IO[Unit] = IO {
    assert(events.size == times, s"Expected $times messages, got ${events.size}")
    events.clear()
  }

  def verifyNoEventsArrived: IO[Unit] = IO {
    events.clear()
  }
}
