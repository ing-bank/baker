package com.ing.baker.types.modules

import com.ing.baker.types.{Converters, Int64}
import org.joda.time.{DateTime, LocalDate, LocalDateTime}
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalatest.prop.Checkers
import org.scalatest.{Matchers, WordSpecLike}

import scala.reflect.runtime.universe.TypeTag

class JodaTimeModuleSpec extends WordSpecLike with Matchers with Checkers {

  def transitivityProp[T : TypeTag](gen: Gen[T]) = forAll(gen) { original =>

    // assertion of the result
    val value = Converters.toValue(original)
    val parsed = Converters.toJava[T](value)

    parsed.equals(original)
  }

  val minSuccessfulTests = 100

  "The JodaTimeModule" should {

    "be able to parse the types of DateTime, LocalDateTime and LocalDate" in {

      Converters.readJavaType[DateTime] shouldBe Int64
      Converters.readJavaType[LocalDateTime] shouldBe Int64
      Converters.readJavaType[LocalDate] shouldBe Int64
    }

    "be able to read/write all DateTime instances" in {

      val dateTimeGen: Gen[DateTime] = Gen.posNum[Long].map(millis => new DateTime(millis))

      check(transitivityProp[DateTime](dateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all LocalDateTime instances" in {

      val localDateTimeGen: Gen[LocalDateTime] = Gen.posNum[Long].map(millis => new LocalDateTime(millis))

      check(transitivityProp[LocalDateTime](localDateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all LocalDate instances" in {

      val localDateGen: Gen[LocalDate] = Gen.posNum[Long].map(millis => new LocalDate(millis))

      check(transitivityProp[LocalDate](localDateGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }
}
