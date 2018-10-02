package com.ing.baker.types.modules

import com.ing.baker.types
import com.ing.baker.types.{Converters, Int64}
import org.joda.time.{DateTime, LocalDate, LocalDateTime}
import org.scalacheck.Gen
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalatest.prop.Checkers
import org.scalatest.{Matchers, WordSpecLike}


class JodaTimeModuleSpec extends WordSpecLike with Matchers with Checkers {

  val minSuccessfulTests = 100

  // Long.MaxValue is not supported by joda time for local dates, resulting in a integer overflow
  // This shifts the long max value 1 bit to the right (divides by 2)
  // This translates to the date: Fri Apr 24 17:36:27 CEST 146140482
  val maxMillis = Long.MaxValue >> 1

  val numGen: Gen[Long] = Gen.chooseNum[Long](
    0L, maxMillis, 0, maxMillis
  )

  "The JodaTimeModule" should {

    "be able to parse the types of DateTime, LocalDateTime and LocalDate" in {

      Converters.readJavaType[DateTime] shouldBe types.Date
      Converters.readJavaType[LocalDateTime] shouldBe types.Date
      Converters.readJavaType[LocalDate] shouldBe types.Date
    }

    "be able to read/write all DateTime instances" in {

      val dateTimeGen: Gen[DateTime] = numGen.map(millis => new DateTime(millis))

      check(transitivityProperty[DateTime](dateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all LocalDateTime instances" in {

      val localDateTimeGen: Gen[LocalDateTime] = numGen.map(millis => new LocalDateTime(millis))

      check(transitivityProperty[LocalDateTime](localDateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all LocalDate instances" in {

      val localDateGen: Gen[LocalDate] = numGen.map(millis => new LocalDate(millis))

      check(transitivityProperty[LocalDate](localDateGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }
}
