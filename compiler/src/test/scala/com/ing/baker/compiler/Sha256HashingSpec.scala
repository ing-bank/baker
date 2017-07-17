package com.ing.baker.compiler

import org.scalacheck.{Prop, Test}
import org.scalatest.{FunSuite, Matchers}

class Sha256HashingSpec extends FunSuite with Matchers {

  test("hash function") {
    val prop = Prop.forAll {
      (s1: String, s2: String) =>{
        if (s1 != s2) Sha256Hashing.hashCode(s1) != Sha256Hashing.hashCode(s2)
        else Sha256Hashing.hashCode(s1) == Sha256Hashing.hashCode(s2)
      }
    }

    prop.check(Test.Parameters.defaultVerbose.withMinSuccessfulTests(100 * 1000))
  }

}
