package com.ing.baker.il

import org.scalacheck.{Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.Checkers

class HashcodeGenerationSpec extends AnyFunSuite with Checkers {
  test("sha256 hash function") {
    val prop = Prop.forAll(Gen.alphaNumStr, Gen.alphaNumStr) {
      (s1: String, s2: String) => {
        if (s1 != s2) hash(s1) != hash(s2)
        else hash(s1) == hash(s2)
      }
    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(100 * 1000))
  }

  private def hash(str: String): Long = sha256HashCode(str)
}
