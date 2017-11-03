package com.ing.baker.il.types

import java.math.BigInteger
import java.util

import org.scalatest.{Matchers, WordSpecLike}
import Converters._

case class PersonCaseClass(name: String, age: Int)

class PersonPojo(val name: String, val age: Int) {
  override def equals(obj: scala.Any): Boolean = obj match {
    case null => false
    case p: PersonPojo => p.name == name && p.age == age
    case _ => false
  }
}

class ConvertersSpec extends WordSpecLike with Matchers {

  "The converters utility" should {

    "be able to parse primitive types" in {
      val primitives = List(
        42,
        Int.box(42),
        42l,
        Long.box(42l),
        42:Short,
        Short.box(42:Short),
        'C',
        Char.box('C'),
        12.34d,
        Double.box(12.34d),
        12.34f,
        Float.box(12.34f),
        "foobar",
        BigDecimal(1.123456789),
        new java.math.BigDecimal(1.123456789),
        BigInt(123456789),
        BigInt(123456789).bigInteger)

      primitives.foreach { obj =>

        asValue(obj) shouldBe PrimitiveValue(obj)
      }
    }

    "be able to parse scala.collection.immutable.List objects" in {

      val list = List(1, 2, 3)
      val expectedValue = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))

      asValue(list) shouldBe expectedValue
    }

    "be able to create scala.collection.immutable.List objects" in {

      val listValue = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))
      val expectedObject = List(1, 2, 3)

      toJava[List[Int]](listValue) shouldBe expectedObject
    }

    "be able to parse java.util.List objects" in {

      val list = new util.ArrayList[Int]()
      list.add(1)
      list.add(2)
      list.add(3)

      val expectedValue = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))

      asValue(list) shouldBe expectedValue
    }

    "be able to create java.util.List objects" in {

      val listValue = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))
      val expectedObject = new util.ArrayList[Int]()
      expectedObject.add(1)
      expectedObject.add(2)
      expectedObject.add(3)

      toJava[java.util.List[Int]](listValue) shouldBe expectedObject
    }

    "be able to parse case class objects" in {

      val person = PersonCaseClass("john", 42)
      val expectedValue = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))

      asValue(person) shouldBe expectedValue
    }

    "be able to create case class objects" in {

      val record = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))
      val expectedObject = PersonCaseClass("john", 42)

      toJava[PersonCaseClass](record) shouldBe expectedObject
    }

    "be able to parse pojo objects" in {

      val obj = new PersonPojo("john", 42)
      val expectedValue = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))

      asValue(obj) shouldBe expectedValue
    }

    "be able to create pojo objects" in {

      val record = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))
      val expectedObject = new PersonPojo("john", 42)

      toJava[PersonPojo](record) shouldBe expectedObject
    }
  }
}
