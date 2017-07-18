package com.ing.baker.il

import org.scalacheck.{Gen, Prop, Test}
import org.scalatest.FunSuite
import org.scalatest.prop.Checkers

class IntermediateLanguageSpec extends FunSuite with Checkers {

//  def hash(str: String): Long = str.hashCode // Test fails with this hash function
  def hash(str: String): Long = sha256HashCode(str)

  test("sha256 hash function") {
    val prop = Prop.forAll(Gen.alphaNumStr, Gen.alphaNumStr) {
      (s1: String, s2: String) => {
        if (s1 != s2) hash(s1) != hash(s2)
        else hash(s1) == hash(s2)
      }
    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(100 * 1000))
  }
}
