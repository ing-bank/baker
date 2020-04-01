package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.serialization.EventJsonToScalaDslDecoders._
import com.ing.baker.types._
import io.circe.parser.decode
import io.circe.syntax._
import org.scalatest.{FunSpec, Matchers}
import com.ing.baker.runtime.serialization.EventJsonEncoders._


class EventJsonToScalaDslDecodersSpec extends FunSpec with Matchers {
  describe("EventJsonToScalaDslDecoders") {
    it("should decode value") {
      val nullValue = decode[Value]("""{"typ":0}""")
      nullValue.right.get shouldEqual NullValue

      val listValue = decode[Value]("""{"typ":1,"val":[{"typ":0}]}""")
      listValue.right.get shouldEqual ListValue(List(NullValue))

      val recordValue = decode[Value]("""{"typ":2,"val":{"key":{"typ":0}}}""")
      recordValue.right.get shouldEqual RecordValue(Map("key" -> NullValue))

      val byteArrayValue = decode[Value]("""{"typ":3,"styp":"ByteArray","val":"f39/"}""")
      byteArrayValue.right.get shouldEqual PrimitiveValue(Array[Byte](127, 127, 127))

      val stringValue = decode[Value]("""{"typ":3,"styp":"java.lang.String","val":"Super String ..."}""")
      stringValue.right.get shouldEqual PrimitiveValue("Super String ...")

      val charValue = decode[Value]("""{"typ":3,"styp":"java.lang.Character","val":"|"}""")
      charValue.right.get shouldEqual PrimitiveValue('|')

      val byteValue = decode[Value]("""{"typ":3,"styp":"java.lang.Byte","val":"99"}""")
      byteValue.right.get shouldEqual PrimitiveValue(99.toByte)

      val intValue = decode[Value]("""{"typ":3,"styp":"java.lang.Integer","val":"10000"}""")
      intValue.right.get shouldEqual PrimitiveValue(10000)

      val floatValue = decode[Value]("""{"typ":3,"styp":"java.lang.Float","val":"1.05"}""")
      floatValue.right.get shouldEqual PrimitiveValue(1.05.toFloat)

      val doubleValue = decode[Value]("""{"typ":3,"styp":"java.lang.Double","val":"111111.05"}""")
      doubleValue.right.get shouldEqual PrimitiveValue(111111.05)

      val booleanValue = decode[Value]("""{"typ":3,"styp":"java.lang.Boolean","val":"false"}""")
      booleanValue.right.get shouldEqual PrimitiveValue(false)

      val shortValue = decode[Value]("""{"typ":3,"styp":"java.lang.Short","val":"600"}""")
      shortValue.right.get shouldEqual PrimitiveValue(600.toShort)

      val longValue = decode[Value]("""{"typ":3,"styp":"java.lang.Long","val":"123456789012345"}""")
      longValue.right.get shouldEqual PrimitiveValue(123456789012345l)
    }

    it("decodes EventInstance") {
      case class ShippingOrder(items: List[String], data: Array[Byte])

      val instance = decode[EventInstance]("""{"name":"ShippingOrder$1","providedIngredients":{"items":{"typ":1,"val":[]},"data":{"typ":3,"styp":"ByteArray","val":"AQU="}}}""").right.get

      instance.name shouldEqual "ShippingOrder$1"
      instance.providedIngredients.size shouldEqual 2
      instance.providedIngredients("items") shouldEqual ListValue(List.empty)
      instance.providedIngredients("data") shouldEqual PrimitiveValue(Array(1.toByte, 5.toByte))
    }
  }
}
