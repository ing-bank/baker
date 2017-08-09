package com.ing.baker.il.petrinet

import org.scalatest.{FunSuite, Matchers}

class MissingEventTransitionSpec extends FunSuite with Matchers {

  test("id is computed") {
    MissingEventTransition("testTransition").id shouldBe -3991477867259255746l
  }

}
