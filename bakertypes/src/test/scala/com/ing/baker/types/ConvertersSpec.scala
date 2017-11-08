package com.ing.baker.types

import java.util
import java.util.Optional

import com.ing.baker.types.Converters._
import org.scalatest.{Matchers, WordSpecLike}

import scala.collection.JavaConverters._

case class PersonCaseClass(name: String, age: Int)

class PersonPojo(val name: String, val age: Int) {
  override def equals(obj: scala.Any): Boolean = obj match {
    case null => false
    case p: PersonPojo => p.name == name && p.age == age
    case _ => false
  }
}

class ConvertersSpec extends WordSpecLike with Matchers {

  val primitiveExamples = List(
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
    BigInt(123456789).bigInteger,
    Array[Byte](-1, 0, 1))

  val recordPerson = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))

  val listValue = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))

  "The converters utility" should {

    "be able to parse primitive types" in {

      primitiveExamples.foreach { obj =>
        toValue(obj) shouldBe PrimitiveValue(obj)
      }
    }

    "be able to create primitive types" in {

      primitiveExamples.foreach { obj =>
        toJava(PrimitiveValue(obj), obj.getClass) shouldBe obj
      }
    }

    "be able to autobox scala Option objects" in {

      toJava[Option[Int]](PrimitiveValue(42)) shouldBe Some(42)
    }

    "be able to autobox java Optional objects" in {

      toJava[Optional[Int]](PrimitiveValue(42)) shouldBe Optional.of(42)
    }

    "be able to parse scala.collection.immutable.List objects" in {

      toValue(List(1, 2, 3)) shouldBe listValue
    }

    "be able to create scala.collection.immutable.List objects" in {

      toJava[List[Int]](listValue) shouldBe List(1, 2, 3)
    }

    "be able to parse java.util.List objects" in {

      val javaList = new util.ArrayList[Int]()
      javaList.add(1)
      javaList.add(2)
      javaList.add(3)

      toValue(javaList) shouldBe listValue
    }

    "be able to create java.util.List objects" in {

      val javaList = new util.ArrayList[Int]()
      javaList.add(1)
      javaList.add(2)
      javaList.add(3)

      toJava[java.util.List[Int]](listValue) shouldBe javaList
    }

    "be able to parse case class objects" in {

      toValue(PersonCaseClass("john", 42)) shouldBe recordPerson
    }

    "be able to create case class objects" in {

      toJava[PersonCaseClass](recordPerson) shouldBe PersonCaseClass("john", 42)
    }

    "be able to parse pojo objects" in {

      toValue(new PersonPojo("john", 42)) shouldBe recordPerson
    }

    "be able to create pojo objects" in {

      toJava[PersonPojo](recordPerson) shouldBe new PersonPojo("john", 42)
    }

    val valueMap = RecordValue(Map(
      "a" -> PrimitiveValue(1),
      "b" -> PrimitiveValue(2),
      "c" -> PrimitiveValue(3)
    ))

    val scalaMap = Map(
      "a" -> 1,
      "b" -> 2,
      "c" -> 3
    )

    val javaMap: util.Map[String, Int] = scalaMap.asJava

    "be able to parse scala.collection.immutable.Map objects" in {

      toValue(scalaMap) shouldBe valueMap
    }

    "be able to create scala.collection.immutable.Map objects" in {

      toJava[Map[String, Int]](valueMap) shouldBe scalaMap
    }


    "be able to parse java.util.Map objects" in {

      toValue(javaMap) shouldBe valueMap
    }

    "be able to create java.util.Map objects" in {

      toJava[java.util.Map[String, Int]](valueMap) shouldBe javaMap
    }
  }
}
