package com.ing.baker.petrinet.api

import com.ing.baker.petrinet.dsl.Place
import org.scalatest.Matchers._
import org.scalatest.WordSpec

class MarkingSpec extends WordSpec {

  type MarkedPlace[P] = (P, MultiSet[Any])

  case class Person(name: String, age: Int)

  val p1 = Place(id = 1)
  val p2 = Place(id = 2)
  val p3 = Place(id = 3)
  val p4 = Place(id = 4)

  def createMarking[P](m1: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1)
  }

  def createMarking[P](m1: MarkedPlace[P], m2: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1, m2)
  }

  def createMarking[P](m1: MarkedPlace[P], m2: MarkedPlace[P], m3: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1, m2, m3)
  }

  "A Colored Marking" should {

    "correctly implement the multiplicity function" in {

      val m = createMarking(p1(1, 2), p2("foo", "bar"))

      m.multiplicities shouldBe Map(p1 -> 2, p2 -> 2)
    }

    "have correct produce semantics" in {

      val m1: Marking[Place] = createMarking(p1(1, 2), p2("foo", "bar"))

      m1 |+| Marking.empty shouldBe m1

      val m2: Marking[Place] = createMarking(p1(3), p2("baz"), p3(1d))

      m1 |+| m2 shouldBe createMarking(p1(3, 1, 2), p2("baz", "foo", "bar"), p3(1d))
    }

    "have correct consume semantics" in {

      val m1: Marking[Place] = createMarking(p1(1, 2, 3), p2("foo", "bar"), p4(Person("Joe", 42)))

      m1 |-| Marking.empty shouldBe m1

      val m2: Marking[Place] = createMarking(p1(2), p4(Person("Joe", 42)))

      m1 |-| m2 shouldBe createMarking(p1(1, 3), p2("foo", "bar"))
    }

    "in case of token value equality only consume tokens equal to the multiplicity" in {

      val m1 = createMarking(p1(1, 1, 1, 1, 1))
      val m2 = createMarking(p1(1, 1))

      m1 |-| m2 shouldBe createMarking(p1(1, 1, 1))
    }
  }
}
