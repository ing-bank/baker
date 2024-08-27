package com.ing.baker.types.modules

import com.ing.baker.types.Converters.{readJavaType, toJava, toValue}
import com.ing.baker.types._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatestplus.scalacheck.Checkers

import java.util.Currency

class CurrencyModulesSpec extends AnyWordSpecLike with Matchers with Checkers {


   "The Currency modules" should {

    "Have the expected type" in {
      readJavaType[Currency] shouldBe RecordType(Seq(
        RecordField("currencyCode", CharArray),
        RecordField("defaultFractionDigits", Int32),
        RecordField("numericCode", Int32)))
    }

    "Pare from and to Currency" in {
      val euro = Currency.getInstance("EUR")
      val euroValue = toValue(euro)
      val recreatedEuro = toJava[Currency](euroValue)
      recreatedEuro shouldBe euro
    }
  }
}
