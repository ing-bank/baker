package com.ing.baker.il

import org.scalacheck.{Prop, Test}
import org.scalatest.FunSuite

class IntermediateLanguageSpec extends FunSuite {

  test("sha256 hash function") {
    val prop = Prop.forAll {
      (s1: String, s2: String) => {
        if (s1 != s2) sha256HashCode(s1) != sha256HashCode(s2)
        else sha256HashCode(s1) == sha256HashCode(s2)
      }
    }

    prop.check(Test.Parameters.defaultVerbose.withMinSuccessfulTests(100 * 1000))
  }
}
