package com.ing.baker.types.modules

import java.util
import java.util.Optional

import com.ing.baker.types
import com.ing.baker.types.Converters._
import com.ing.baker.types.ConvertersTestData.TestEnum
import com.ing.baker.types.ConvertersTestData.TestEnum.{ValueA, ValueB, ValueC}
import com.ing.baker.types._
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

class JavaModulesSpec extends WordSpecLike with Matchers {

  val recordPerson = RecordValue(Map("name" -> PrimitiveValue("john"), "age" -> PrimitiveValue(42)))

  val listValue123 = ListValue(List(PrimitiveValue(1), PrimitiveValue(2), PrimitiveValue(3)))

  val listValueABC = ListValue(List(PrimitiveValue("a"), PrimitiveValue("b"), PrimitiveValue("c")))

  val listValueForEnumABC = ListValue(List(PrimitiveValue(ValueA.name()), PrimitiveValue(ValueB.name()), PrimitiveValue(ValueC.name())))

  val mapValue = RecordValue(Map(
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

  "The converters utility" should {

    "be able to autobox null values to java Optionals" in {

      toJava[Optional[Int]](NullValue) shouldBe Optional.empty
    }

    "be able to autobox primitive values to java Optionals" in {

      toJava[Optional[Int]](PrimitiveValue(42)) shouldBe Optional.of(42)
    }

    "be able to read java Optional.empty()" in {
      toValue(Optional.empty()) shouldBe NullValue
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

    "be able to create java.util.List<T> objects" in {

      val javaList = new util.ArrayList[String]()
      javaList.add("a")
      javaList.add("b")
      javaList.add("c")

      listValueABC.asList(classOf[String]) shouldBe javaList
    }

    "be able to create java.util.Set<T> objects" in {

      val javaSet = new util.HashSet[String]()
      javaSet.add("a")
      javaSet.add("b")
      javaSet.add("c")

      listValueABC.asSet(classOf[String]) shouldBe javaSet
    }

    "be able to create java.util.Map<K, V> objects" in {

      val javaMap = new util.HashMap[String, Integer]()
      javaMap.put("a", 1)
      javaMap.put("b", 2)
      javaMap.put("c", 3)

      mapValue.asMap(classOf[String], classOf[java.lang.Integer]) shouldBe javaMap
    }

    "fail to convert a unsupported value into a java List<T>/Set<T>/Map<K, V> objects" in {
      intercept[IllegalArgumentException] (PrimitiveValue("a").asList(classOf[String]))
        .getMessage shouldBe "value of type class com.ing.baker.types.PrimitiveValue cannot be converted to a java.util.List object"

      intercept[IllegalArgumentException] (PrimitiveValue("a").asSet(classOf[String]))
        .getMessage shouldBe "value of type class com.ing.baker.types.PrimitiveValue cannot be converted to a java.util.Set object"

      intercept[IllegalArgumentException] (PrimitiveValue("a").asMap(classOf[String], classOf[java.lang.Integer]))
        .getMessage shouldBe "value of type class com.ing.baker.types.PrimitiveValue cannot be converted to a java.util.Map object"
    }

    "be able to parse pojo objects" in {

      toValue(new PersonPojo("john", 42)) shouldBe recordPerson
    }

    "be able to create pojo objects" in {

      toJava[PersonPojo](recordPerson) shouldBe new PersonPojo("john", 42)
    }

    "be able to parse java.util.Map objects" in {

      toValue(javaMap) shouldBe mapValue
    }

    "be able to create java.util.Map objects" in {

      toJava[java.util.Map[String, Int]](mapValue) shouldBe javaMap
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
