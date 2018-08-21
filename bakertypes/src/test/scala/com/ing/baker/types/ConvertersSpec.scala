package com.ing.baker.types

import java.util
import java.util.Optional

import com.ing.baker.types
import com.ing.baker.types.Converters._
import com.ing.baker.types.ConvertersTestData.TestEnum
import com.ing.baker.types.ConvertersTestData.TestEnum.{ValueA, ValueB, ValueC}
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
    scala.Char.box('C'),
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

  val listValue123 = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))

  val listValueABC = ListValue(List(PrimitiveValue("a"), PrimitiveValue("b"), PrimitiveValue("c")))

  val listValueForEnumABC = ListValue(List(PrimitiveValue(ValueA.name()), PrimitiveValue(ValueB.name()), PrimitiveValue(ValueC.name())))

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

    "be able to read scala.Option.None" in {
      toValue(None) shouldBe NullValue
    }

    "be able to read java Optional.empty()" in {
      toValue(Optional.empty()) shouldBe NullValue
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

    "be able to parse java.util.Set objects" in {

      val javaSet = new util.HashSet[String]()
      javaSet.add("a")
      javaSet.add("b")
      javaSet.add("c")

      toValue(javaSet) shouldBe listValueABC
    }

    "be able to create java.util.Set objects" in {

      val javaSet = new util.HashSet[String]()
      javaSet.add("a")
      javaSet.add("b")
      javaSet.add("c")

      toJava[java.util.Set[String]](listValueABC) shouldBe javaSet
    }

    "be able to parse java.util.Set with enums" in {

      val javaSet: util.Set[TestEnum] = new util.HashSet[TestEnum]()
      javaSet.add(ValueA)
      javaSet.add(ValueB)
      javaSet.add(ValueC)

      val actualListValue = toValue(javaSet).asInstanceOf[ListValue] // we know java.util.Set is represented as a ListValue

      // Here we need to sor the elements because the List representation sometimes has a different order than the original Set entries
      actualListValue.entries.map(_.toString).sorted shouldBe listValueForEnumABC.entries.map(_.toString).sorted
    }

    "be able to create java.util.Set enums" in {

      val expectedJavaSet: util.Set[TestEnum] = new util.HashSet[TestEnum]()
      expectedJavaSet.add(ValueA)
      expectedJavaSet.add(ValueB)
      expectedJavaSet.add(ValueC)

      val actualSet: util.Set[TestEnum] = toJava[util.Set[TestEnum]](listValueForEnumABC)

      actualSet shouldBe expectedJavaSet
    }

    "be able to parse java.util.EnumSet objects" in {

      val javaEnumSet = util.EnumSet.of(ValueA, ValueB, ValueC)

      toValue(javaEnumSet) shouldBe listValueForEnumABC
    }

    // This test is ignored because Baker does not support java.util.EnumSet
    "be able to create java.util.EnumSet objects" ignore {

      val expectedJavaEnumSet: util.EnumSet[TestEnum] = util.EnumSet.of(ValueA, ValueB, ValueC)

      val actualSet: util.EnumSet[TestEnum] = toJava[util.EnumSet[TestEnum]](listValueForEnumABC)

      actualSet shouldBe expectedJavaEnumSet
    }

    "be able to parse java.util.List objects" in {

      val javaList = new util.ArrayList[Int]()
      javaList.add(1)
      javaList.add(2)
      javaList.add(3)

      toValue(javaList) shouldBe listValue123
    }

    "be able to create java.util.List objects" in {

      val javaList = new util.ArrayList[Int]()
      javaList.add(1)
      javaList.add(2)
      javaList.add(3)

      toJava[java.util.List[Int]](listValue123) shouldBe javaList
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

    "correctly parse all the supported base types" in {

      primitiveMappings.foreach {
        case (clazz, t) => readJavaType(clazz) shouldBe t
      }
    }

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

    "correctly parse array of bytes" in {
      readJavaType[Array[Byte]] shouldBe types.ByteArray
    }

    "correctly parse enum types" in {
      readJavaType[EnumExample] shouldBe EnumType(options = Set("A", "B", "C"))
    }

    "correctly parse basic POJO types" in {
      val simplePOJOFields = Seq(
        RecordField("integer", types.Int32),
        RecordField("string", types.CharArray),
        RecordField("boolean", types.Bool))

      readJavaType[SimplePOJOExample] shouldBe RecordType(simplePOJOFields)
    }

    "correctly parse POJO types in POJO types" in {
      val simplePOJOExampleSeq = Seq(
        RecordField("integer", types.Int32),
        RecordField("string", types.CharArray),
        RecordField("boolean", types.Bool))

      val complexPOJOExampleSeq = Seq(
        RecordField("simplePOJOExample", RecordType(simplePOJOExampleSeq)),
        RecordField("string", types.CharArray),
        RecordField("boolean", types.Bool))

      readJavaType[ComplexPOJOExample] shouldBe RecordType(complexPOJOExampleSeq)
    }
  }
}
