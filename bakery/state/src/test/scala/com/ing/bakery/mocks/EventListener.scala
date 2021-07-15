package com.ing.bakery.mocks

import cats.effect.IO
import com.ing.baker.runtime.common.{BakerEvent, EventInstance}
import com.ing.bakery.baker.EventSink

import scala.collection.mutable

class EventListener {

  val events: mutable.ListBuffer[String] = mutable.ListBuffer.empty[String]

  val eventSink: EventSink = new EventSink() {

    def fire(event: Any): IO[Unit] = {
      event match {
        case _: BakerEvent     =>
        case _: EventInstance  =>
          events.append(event.toString)
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
