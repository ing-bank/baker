package com.ing.baker.test.scaladsl

import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class BakerEventsFlowTest extends AnyFlatSpec with Matchers {

  "BakerEventsFlow object" should "be created" in {
    val flow = "a" :: "B" :: "C" :: EmptyFlow
    val anotherFlow = "D" :: EmptyFlow
    assertResult(BakerEventsFlow("a", "B", "C"))(flow)
    assertResult(BakerEventsFlow("a", "B", "C", "D"))(flow ::: anotherFlow)
    assertResult(BakerEventsFlow("a"))(flow -- "B" -- "C")
    assertResult(BakerEventsFlow("a"))(flow --- ("B" :: "C" :: EmptyFlow))
  }

  "BakerEventsFlow object" should "be tested for equals" in {
    val expected = "Object" :: "BakerEventsFlow" :: "bla" :: EmptyFlow
    val actual = classOf[Object] :: classOf[BakerEventsFlow] :: "bla" :: EmptyFlow
    assertResult(expected)(actual)
  }

  "BakerEventsFlow object" should "be tested for equals and order should not matter" in {
    val expected = "Object" :: "BakerEventsFlow" :: "bla" :: EmptyFlow
    val actual = "bla" :: classOf[BakerEventsFlow] :: classOf[Object] :: "bla" :: EmptyFlow
    assertResult(expected)(actual)
  }
}

