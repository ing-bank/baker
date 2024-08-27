package com.ing.baker.types.modules

import com.ing.baker.types
import com.ing.baker.types.{Converters, Int32, Int64, RecordField, RecordValue, Value}

import java.time.{Duration, Instant, LocalDate, LocalDateTime, OffsetDateTime, ZoneId, ZonedDateTime}
import org.scalacheck.Gen
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatestplus.scalacheck.Checkers

class JavaTimeModuleSpec extends AnyWordSpecLike with Matchers with Checkers {

  private val minSuccessfulTests = 100

  // Long.MaxValue is not supported by joda time for local dates, resulting in a integer overflow
  // This shifts the long max value 1 bit to the right (divides by 2)
  // This translates to the date: Fri Apr 24 17:36:27 CEST 146140482
  private val maxMillis = Long.MaxValue >> 1

  private val numGen: Gen[Long] = Gen.chooseNum[Long](
    0L, maxMillis, 0, maxMillis
  )

  "The JavaTimeModule" should {

    "be able to parse the types of DateTime, LocalDateTime and LocalDate" in {
      Converters.readJavaType[java.util.Date] shouldBe types.Date
      Converters.readJavaType[LocalDate] shouldBe types.Date
      Converters.readJavaType[LocalDateTime] shouldBe types.Date
      Converters.readJavaType[OffsetDateTime] shouldBe types.Date
      Converters.readJavaType[ZonedDateTime] shouldBe types.Date
      Converters.readJavaType[Instant] shouldBe types.Date
    }

    "be able to read/write all java.util.Date instances" in {

      val dateGen: Gen[java.util.Date] = numGen.map(millis => java.util.Date.from(Instant.ofEpochMilli(millis)))

      check(transitivityProperty[java.util.Date](dateGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }


    "be able to read/write all LocalDate instances" in {

      val localDateGen: Gen[LocalDate] = numGen.map(millis => LocalDate.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault()))

      check(transitivityProperty[LocalDate](localDateGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all LocalDateTime instances" in {

      val localDateTimeGen: Gen[LocalDateTime] = numGen.map(millis => LocalDateTime.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault()))

      check(transitivityProperty[LocalDateTime](localDateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all OffsetDateTime instances" in {

      val offsetDateTimeGen: Gen[OffsetDateTime] = numGen.map(millis => OffsetDateTime.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault()))

      check(transitivityProperty[OffsetDateTime](offsetDateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all ZonedDateTime instances" in {

      val offsetDateTimeGen: Gen[ZonedDateTime] = numGen.map(millis => ZonedDateTime.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault()))

      check(transitivityProperty[ZonedDateTime](offsetDateTimeGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write all Instant instances" in {

      val instantGen: Gen[Instant] = numGen.map(millis => Instant.ofEpochMilli(millis))

      check(transitivityProperty[Instant](instantGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }
}
