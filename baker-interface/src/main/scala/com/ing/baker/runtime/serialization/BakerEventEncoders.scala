package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.types
import io.circe.Encoder._
import io.circe._
import io.circe.generic.semiauto._

object BakerEventEncoders {

  implicit def ValuesEncoder: Encoder[types.Value] =
    Encoder.instance {
      case types.NullValue =>
        Json.Null
      case types.ListValue(entries) =>
        encodeList(ValuesEncoder)(entries)
      case types.RecordValue(entries) =>
        encodeMap(KeyEncoder.encodeKeyString, ValuesEncoder)(entries)
      case types.PrimitiveValue(value) =>
        encodeString(value.toString)
    }

  implicit val bakerEventEncoder: Encoder[BakerEvent] = deriveEncoder[BakerEvent]
}