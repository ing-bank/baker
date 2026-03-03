package com.ing.baker.il.petrinet

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers


class MissingEventTransitionSpec extends AnyFunSuite with Matchers {

  test("id is computed") {
    MissingEventTransition("testTransition").id shouldBe -3991477867259255746L
  }

}
