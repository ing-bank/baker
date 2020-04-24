package com.ing.baker.test.javadsl

import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class BakerEventsFlowTest extends AnyFlatSpec with Matchers {
  "BakerEventsFlow object" should "be created" in {
    BakerEventsFlow.of("a", "b", "c")
    BakerEventsFlow.ofClass(classOf[Object])
  }

  "BakerEventsFlow object" should "be test for equals" in {
    val result = BakerEventsFlow.of("Object", "BakerEventsFlowTest") ==
      BakerEventsFlow.ofClass(classOf[Object], classOf[BakerEventsFlowTest])
    assertResult(true)(result)
  }

  "BakerEventsFlow object" should "be test for equals and order should not matter" in {
    val result = BakerEventsFlow.of("BakerEventsFlowTest", "Object") ==
      BakerEventsFlow.ofClass(classOf[Object], classOf[BakerEventsFlowTest])
    assertResult(true)(result)
  }
}
