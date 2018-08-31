package com.ing.baker.types.modules

import java.lang

import com.ing.baker.types
import com.ing.baker.types.Converters.readJavaType
import com.ing.baker.types.modules.PrimitiveModuleSpec._
import org.scalacheck.Gen
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalatest.prop.Checkers
import org.scalatest.{Matchers, WordSpecLike}

import scala.reflect.runtime.universe.TypeTag

object PrimitiveModuleSpec {

  val intGen: Gen[Int] = Gen.chooseNum[Int](Integer.MIN_VALUE, Integer.MAX_VALUE)
  val langIntegerGen: Gen[lang.Integer] = intGen.map(Int.box(_))
  val longGen: Gen[Long] = Gen.chooseNum[Long](Long.MinValue, Long.MaxValue)
  val langLongGen: Gen[lang.Long] = Gen.chooseNum[Long](Long.MinValue, Long.MaxValue).map(Long.box(_))
  val shortGen: Gen[Short] = Gen.chooseNum[Short](Short.MinValue, Short.MaxValue)
  val langShortGen: Gen[lang.Short] = shortGen.map(Short.box(_))
  val floatGen: Gen[Float] = Gen.chooseNum(Float.MinValue, Float.MaxValue)
  val langFloatGen: Gen[lang.Float] = floatGen.map(Float.box(_))
  val doubleGen: Gen[Double] = Gen.chooseNum[Double](Double.MinValue, Double.MaxValue)
  val langDoubleGen: Gen[lang.Double] = doubleGen.map(Double.box(_))
  val stringGen: Gen[String] = Gen.alphaStr
  val bigIntGen: Gen[BigInt] = longGen.map(BigInt(_))
  val javaBigIntGen: Gen[java.math.BigInteger] = bigIntGen.map(_.bigInteger)
  val bigDecimalGen: Gen[BigDecimal] = doubleGen.map(BigDecimal(_))
  val javaBigDecimalGen: Gen[java.math.BigDecimal] = bigDecimalGen.map(_.bigDecimal)
  val byteArrayGen: Gen[Array[Byte]] = Gen.listOf(intGen.map(_.toByte)).map(_.toArray)
}

class PrimitiveModuleSpec extends WordSpecLike with Matchers with Checkers {

  "The primivite module" should {

    "correctly parse all the supported primitive types" in {

      readJavaType[Int] shouldBe types.Int32
      readJavaType[lang.Integer] shouldBe types.Int32
      readJavaType[Long] shouldBe types.Int64
      readJavaType[lang.Long] shouldBe types.Int64
      readJavaType[Short] shouldBe types.Int16
      readJavaType[lang.Short] shouldBe types.Int16
      readJavaType[Float] shouldBe types.Float32
      readJavaType[lang.Float] shouldBe types.Float32
      readJavaType[Double] shouldBe types.Float64
      readJavaType[lang.Double] shouldBe types.Float64
      readJavaType[String] shouldBe types.CharArray
      readJavaType[BigInt] shouldBe types.IntBig
      readJavaType[java.math.BigInteger] shouldBe types.IntBig
      readJavaType[BigDecimal] shouldBe types.FloatBig
      readJavaType[java.math.BigDecimal] shouldBe types.FloatBig
      readJavaType[Array[Byte]] shouldBe types.ByteArray
    }

    "read/write all supported primitive types" in {

      val minSuccessful = 100

      def checkTransitivity[T : TypeTag](gen: Gen[T]) =
        check(transitivityProperty[Int](intGen), defaultVerbose.withMinSuccessfulTests(minSuccessful))

      checkTransitivity[Int](intGen)
      checkTransitivity[lang.Integer](langIntegerGen)
      checkTransitivity[Long](longGen)
      checkTransitivity[lang.Long](langLongGen)
      checkTransitivity[Short](shortGen)
      checkTransitivity[lang.Short](langShortGen)
      checkTransitivity[Float](floatGen)
      checkTransitivity[lang.Float](langFloatGen)
      checkTransitivity[Double](doubleGen)
      checkTransitivity[lang.Double](langDoubleGen)
      checkTransitivity[String](stringGen)
      checkTransitivity[BigInt](bigIntGen)
      checkTransitivity[java.math.BigInteger](javaBigIntGen)
      checkTransitivity[BigDecimal](bigDecimalGen)
      checkTransitivity[java.math.BigDecimal](javaBigDecimalGen)
      checkTransitivity[Array[Byte]](byteArrayGen)
    }
  }
}
