package com.ing.baker.types.modules

import com.ing.baker.types
import com.ing.baker.types.Converters.{readJavaType, toJava, toValue}
import com.ing.baker.types._
import org.scalatest.prop.Checkers
import org.scalatest.{Matchers, WordSpecLike}

class ScalaModulesSpec extends WordSpecLike with Matchers with Checkers {

  val listValue123 = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))

  val recordPerson = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))

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

  "The scala modules" should {

    "correctly parse option types" in {
      readJavaType[Option[String]] shouldBe OptionType(types.CharArray)
    }

    "correctly parse list types" in {
      readJavaType[List[String]] shouldBe ListType(types.CharArray)
    }

    "correctly parse set types" in {

      readJavaType[Set[String]] shouldBe ListType(types.CharArray)
      readJavaType[java.util.Set[String]] shouldBe ListType(types.CharArray)
    }

    "be able to autobox null values to scala Options" in {

      toJava[Option[Int]](NullValue) shouldBe None
    }

    "be able to autobox primitive values to scala Options" in {

      toJava[Option[Int]](PrimitiveValue(42)) shouldBe Some(42)
    }

    "be able to read scala.Option.None" in {
      toValue(None) shouldBe NullValue
    }

    "be able to parse scala.collection.immutable.List objects" in {

      toValue(List(1, 2, 3)) shouldBe listValue123
    }

    "be able to create scala.collection.immutable.List objects" in {

      toJava[List[Int]](listValue123) shouldBe List(1, 2, 3)
    }

    "be able to parse scala.collection.immutable.Set objects" in {

      toValue(Set(1, 2, 3)) shouldBe listValue123
    }

    "be able to create scala.collection.immutable.Set objects" in {

      toJava[Set[Int]](listValue123) shouldBe Set(1, 2, 3)
    }

    "be able to parse case class objects" in {

      toValue(PersonCaseClass("john", 42)) shouldBe recordPerson
    }

    "be able to create case class objects" in {

      toJava[PersonCaseClass](recordPerson) shouldBe PersonCaseClass("john", 42)
    }

    "be able to parse scala.collection.immutable.Map objects" in {

      toValue(scalaMap) shouldBe valueMap
    }

    "be able to create scala.collection.immutable.Map objects" in {

      toJava[Map[String, Int]](valueMap) shouldBe scalaMap
    }
  }
}
