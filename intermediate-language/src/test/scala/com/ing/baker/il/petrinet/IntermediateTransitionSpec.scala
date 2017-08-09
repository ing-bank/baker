package com.ing.baker.il.petrinet

import org.scalatest.{FunSuite, Matchers}

class IntermediateTransitionSpec extends FunSuite with Matchers {

  test("id is computed") {
    IntermediateTransition("testTransition").id shouldBe -401713565417492236l
  }

}
