package com.ing.baker.runtime.actortyped.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.google.protobuf.ByteString
import com.ing.baker.types
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actor.protobuf
import protobuf.Value.OneofValue._
import org.joda.time.{LocalDate, LocalDateTime, LocalTime}
import org.joda.time.format.ISODateTimeFormat

import scala.util.{Failure, Success, Try}

class BakerValuesMapping extends ProtobufMapping[types.Value, protobuf.Value] {

  def toProto(t: types.Value): protobuf.Value = protobuf.Value(t match {

    case types.NullValue =>
      NullValue(true)

    case types.PrimitiveValue(value: Boolean) =>
      BooleanValue(value)

    case types.PrimitiveValue(value: Byte) =>
      ByteValue(value)

    case types.PrimitiveValue(value: Short) =>
      ShortValue(value)

    case types.PrimitiveValue(value: Char) =>
      CharValue(value)

    case types.PrimitiveValue(value: Int) =>
      IntValue(value)

    case types.PrimitiveValue(value: Long) =>
      LongValue(value)

    case types.PrimitiveValue(value: Float) =>
      FloatValue(value)

    case types.PrimitiveValue(value: Double) =>
      DoubleValue(value)

    case types.PrimitiveValue(value: String) =>
      StringValue(value)

    case types.PrimitiveValue(value: BigDecimal) =>
      BigDecimalScalaValue(value.toString())

    case types.PrimitiveValue(value: java.math.BigDecimal) =>
      BigDecimalJavaValue(BigDecimal(value).toString())

    case types.PrimitiveValue(value: BigInt) =>
      BigIntScalaValue(value.toString())

    case types.PrimitiveValue(value: java.math.BigInteger) =>
      BigIntJavaValue(BigInt(value).toString())

    case types.PrimitiveValue(value: Array[Byte]) =>
      ByteArrayValue(ByteString.copyFrom(value))

    case types.PrimitiveValue(value) =>
      throw new IllegalStateException(s"Unknown primitive value of type: ${value.getClass}")

    case types.RecordValue(entries) =>
      RecordValue(protobuf.Record(entries.mapValues(toProto)))

    case types.ListValue(entries) =>
      ListValue(protobuf.List(entries.map(toProto)))

  })

  def fromProto(message: protobuf.Value): Try[types.Value] = message.oneofValue match {
    case NullValue(_) =>
      Success(types.NullValue)

    case BooleanValue(bool) =>
      Success(types.PrimitiveValue(bool))

    case ByteValue(byte) =>
      Success(types.PrimitiveValue(byte.toByte))

    case ShortValue(short) =>
      Success(types.PrimitiveValue(short.toShort))

    case CharValue(char) =>
      Success(types.PrimitiveValue(char.toChar))

    case IntValue(int) =>
      Success(types.PrimitiveValue(int))

    case LongValue(long) =>
      Success(types.PrimitiveValue(long))

    case FloatValue(float) =>
      Success(types.PrimitiveValue(float))

    case DoubleValue(double) =>
      Success(types.PrimitiveValue(double))

    case StringValue(string) =>
      Success(types.PrimitiveValue(string))

    case BigDecimalScalaValue(bigdecimal) =>
      Success(types.PrimitiveValue(BigDecimal(bigdecimal)))

    case BigDecimalJavaValue(bigdecimal) =>
      Success(types.PrimitiveValue(BigDecimal(bigdecimal).bigDecimal))

    case BigIntScalaValue(bigint) =>
      Success(types.PrimitiveValue(BigInt(bigint)))

    case BigIntJavaValue(bigint) =>
      Success(types.PrimitiveValue(BigInt(bigint).bigInteger))

    case ByteArrayValue(byteArray) =>
      Success(types.PrimitiveValue(byteArray.toByteArray))

    case RecordValue(protobuf.Record(fields)) =>
      fields.toList.traverse[Try, (String, types.Value)] {
        case (key, value) => fromProto(value).map(key -> _)
      }.map(inner => types.RecordValue(inner.toMap))

    // deprecated fields
    case ListValue(protobuf.List(entries)) =>
      entries.toList.traverse[Try, types.Value](fromProto).map(types.ListValue)

    case JodaDatetimeValue(date) =>
      val dateTime = ISODateTimeFormat.dateTime().parseDateTime(date)
      Success(types.PrimitiveValue(dateTime.getMillis))

    case JodaLocaldateValue(date) =>
      val localDate = LocalDate.parse(date)
      Success(types.PrimitiveValue(localDate.toDateTime(LocalTime.MIDNIGHT).getMillis))

    case JodaLocaldatetimeValue(date) =>
      val localDateTime = LocalDateTime.parse(date)
      Success(types.PrimitiveValue(localDateTime.toDateTime.getMillis))

    case Empty =>
      Failure(new IllegalStateException("Empty value cannot be deserialized"))
  }

}

