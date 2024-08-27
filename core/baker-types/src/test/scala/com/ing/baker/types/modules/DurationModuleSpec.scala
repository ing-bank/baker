package com.ing.baker.types.modules

import com.ing.baker.types
import com.ing.baker.types._
import org.scalacheck.Gen
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatestplus.scalacheck.Checkers

import java.time._

class DurationModuleSpec extends AnyWordSpecLike with Matchers with Checkers {

  private val minSuccessfulTests = 100

  // Long.MaxValue is not supported by joda time for local dates, resulting in a integer overflow
  // This shifts the long max value 1 bit to the right (divides by 2)
  // This translates to the date: Fri Apr 24 17:36:27 CEST 146140482
  private val maxMillis = Long.MaxValue >> 1

  private val numGen: Gen[Long] = Gen.chooseNum[Long](
    0L, maxMillis, 0, maxMillis
  )

  "The DurationModule" should {

    "be able to parse the types of Duration" in {
      Converters.readJavaType[Duration] shouldBe types.RecordType(Seq(RecordField("seconds", Int64), RecordField("nanos", Int32)))
    }

    "be able to read/write all Duration instances" in {

      val durationGen: Gen[Duration] = numGen.map(millis => Duration.ofMillis(millis))

      check(transitivityProperty[Duration](durationGen), defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }

    "be able to read/write original POJO Duration instances" in {
      val duration: Duration = Duration.ofNanos(11000000001L)
      val value: Value = Converters.toValue(duration)
      val converted = value.as(classOf[Duration])
      duration shouldBe converted

      val durationValue: RecordValue = RecordValue(Map("seconds" -> Converters.toValue(11L), "nanos" -> Converters.toValue(1)))
      val newDuration = durationValue.as(classOf[Duration])
      newDuration shouldBe duration
    }
  }
}
