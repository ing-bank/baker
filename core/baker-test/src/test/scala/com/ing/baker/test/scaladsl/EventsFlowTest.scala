package com.ing.baker.test.scaladsl

import com.ing.baker.test.{EmptyFlow, EventsFlow}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class EventsFlowTest extends AnyFlatSpec with Matchers {

  "BakerEventsFlow object" should "be created" in {
    val flow = "a" :: "B" :: "C" :: EmptyFlow
    val anotherFlow = "D" :: EmptyFlow
    val d = flow ::: anotherFlow
    assertResult(EventsFlow("a", "B", "C"))(flow)
    assertResult(EventsFlow("a", "B", "C", "D"))(d)
    assertResult(EventsFlow("a"))(flow -- "B" -- "C")
    assertResult(EventsFlow("a"))(flow --- ("B" :: "C" :: EmptyFlow))
  }

  "BakerEventsFlow object" should "be tested for equals" in {
    val expected = "Object" :: "EventsFlow" :: "bla" :: EmptyFlow
    val actual = classOf[Object] :: classOf[EventsFlow] :: "bla" :: EmptyFlow
    assertResult(expected)(actual)
  }

  "BakerEventsFlow object" should "be tested for equals and order should not matter" in {
    val expected = "Object" :: "EventsFlow" :: "bla" :: EmptyFlow
    val actual = "bla" :: classOf[EventsFlow] :: classOf[Object] :: "bla" :: EmptyFlow
    assertResult(expected)(actual)
  }
}