package com.ing.baker.petrinet.api

import org.scalatest.Matchers._
import org.scalatest.WordSpec

class MarkingSpec extends WordSpec {

  case class Person(name: String, age: Int)

  type Place = Int

  val p1 = 1
  val p2 = 2
  val p3 = 3
  val p4 = 4

  "A Colored Marking" should {

    "correctly implement the multiplicity function" in {

      val m: Marking[Place] = Map(
        p1 -> MultiSet(1, 2),
        p2 -> MultiSet("foo", "bar"))

      m.multiplicities shouldBe Map(p1 -> 2, p2 -> 2)
    }

    "have correct produce semantics" in {

      val m1: Marking[Place] = Map(
        p1 -> MultiSet(1, 2),
        p2 -> MultiSet("foo", "bar"))

      m1 |+| Marking.empty shouldBe m1

      val m2: Marking[Place] = Map(
        p1 -> MultiSet(3),
        p2 -> MultiSet("baz"),
        p3 -> MultiSet(1d))

      val expected: Marking[Place] = Map(
        p1 -> MultiSet(3, 1, 2),
        p2 -> MultiSet("baz", "foo", "bar"),
        p3 -> MultiSet(1d))

      m1 |+| m2 shouldBe expected
    }

    "have correct consume semantics" in {

      val m1: Marking[Place] = Map(
        p1 -> MultiSet(1, 2, 3),
        p2 -> MultiSet("foo", "bar"),
        p4 -> MultiSet(Person("Joe", 42)))

      m1 |-| Marking.empty shouldBe m1

      val m2: Marking[Place] = Map(
        p1 -> MultiSet(2),
        p4 -> MultiSet(Person("Joe", 42)))

      val expected: Marking[Place] = Map(
        p1 -> MultiSet(1, 3),
        p2 -> MultiSet("foo", "bar"))

      m1 |-| m2 shouldBe expected
    }

    "in case of token value equality only consume tokens equal to the multiplicity" in {

      val m1: Marking[Place] = Map(p1 -> MultiSet(1, 1, 1, 1, 1))
      val m2: Marking[Place] = Map(p1 -> MultiSet(1, 1))

      m1 |-| m2 shouldBe Map(p1 -> MultiSet(1, 1, 1))
    }
  }
}
