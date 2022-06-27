package com.ing.baker.il.petrinet

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers


class IntermediateTransitionSpec extends AnyFunSuite with Matchers {

  test("id is computed") {
    IntermediateTransition("testTransition").id shouldBe -401713565417492236L
  }

}
