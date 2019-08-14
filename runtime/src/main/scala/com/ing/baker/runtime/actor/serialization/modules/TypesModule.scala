package com.ing.baker.runtime.actor.serialization.modules

import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf._
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.types
import org.joda.time.format.ISODateTimeFormat
import org.joda.time.{LocalDate, LocalDateTime, LocalTime}

class TypesModule extends ProtoEventAdapterModule {

  private def createPrimitive(p: PrimitiveType) = protobuf.Type(Type.OneofType.Primitive(p))

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {

    case types.Bool => createPrimitive(PrimitiveType.BOOL)
    case types.Byte => createPrimitive(PrimitiveType.BYTE)
    case types.Int16 => createPrimitive(PrimitiveType.INT16)
    case types.Char => createPrimitive(PrimitiveType.CHAR)
    case types.Int32 => createPrimitive(PrimitiveType.INT)
    case types.Int64 => createPrimitive(PrimitiveType.INT64)
    case types.Float32 => createPrimitive(PrimitiveType.FLOAT32)
    case types.Float64 => createPrimitive(PrimitiveType.FLOAT64)
    case types.CharArray => createPrimitive(PrimitiveType.CHAR_ARRAY)
    case types.FloatBig => createPrimitive(PrimitiveType.FLOAT_BIG)
    case types.IntBig => createPrimitive(PrimitiveType.INT_BIG)
    case types.ByteArray => createPrimitive(PrimitiveType.BYTE_ARRAY)
    case types.Date => createPrimitive(PrimitiveType.DATE)

    case types.OptionType(entryType) =>
      val entryProto = ctx.toProto[protobuf.Type](entryType)
      protobuf.Type(Type.OneofType.Optional(OptionalType(Some(entryProto))))

    case types.ListType(entryType) =>
      val entryProto = ctx.toProto[protobuf.Type](entryType)
      protobuf.Type(Type.OneofType.List(ListType(Some(entryProto))))

    case types.RecordType(fields) =>

      val protoFields = fields.map { f =>
        val protoType = ctx.toProto[protobuf.Type](f.`type`)
        protobuf.RecordField(Some(f.name), Some(protoType))
      }

      protobuf.Type(Type.OneofType.Record(RecordType(protoFields)))

    case types.MapType(valueType) =>
      val valueProto = ctx.toProto[protobuf.Type](valueType)
      protobuf.Type(Type.OneofType.Map(MapType(Some(valueProto))))

    case types.EnumType(options) =>
      protobuf.Type(Type.OneofType.Enum(EnumType(options.toSeq)))

    case v: types.Value =>

      import protobuf.Value.OneofValue._

      val oneof: protobuf.Value.OneofValue = v match {
        case types.NullValue => (NullValue(true))
        case types.PrimitiveValue(value: Boolean) => BooleanValue(value)
        case types.PrimitiveValue(value: Byte) => ByteValue(value)
        case types.PrimitiveValue(value: Short) => ShortValue(value)
        case types.PrimitiveValue(value: Char) => CharValue(value)
        case types.PrimitiveValue(value: Int) => IntValue(value)
        case types.PrimitiveValue(value: Long) => LongValue(value)
        case types.PrimitiveValue(value: Float) => FloatValue(value)
        case types.PrimitiveValue(value: Double) => DoubleValue(value)
        case types.PrimitiveValue(value: String) => StringValue(value)
        case types.PrimitiveValue(value: BigDecimal) => BigDecimalScalaValue(value.toString())
        case types.PrimitiveValue(value: java.math.BigDecimal) => BigDecimalJavaValue(BigDecimal(value).toString())
        case types.PrimitiveValue(value: BigInt) => BigIntScalaValue(value.toString())
        case types.PrimitiveValue(value: java.math.BigInteger) => BigIntJavaValue(BigInt(value).toString())
        case types.PrimitiveValue(value: Array[Byte]) => ByteArrayValue(ByteString.copyFrom(value))
        case types.PrimitiveValue(value) => throw new IllegalStateException(s"Unknown primitive value of type: ${value.getClass}")
        case types.RecordValue(entries) => RecordValue(protobuf.Record(entries.mapValues(ctx.toProto[protobuf.Value])))
        case types.ListValue(entries) => ListValue(protobuf.List(entries.map(ctx.toProto[protobuf.Value])))
      }

      protobuf.Value(oneof)
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {

    case msg: protobuf.Type =>

      import Type.OneofType._
      import PrimitiveType._

      msg.`oneofType` match {

        case Primitive(BOOL) => types.Bool
        case Primitive(BYTE) => types.Byte
        case Primitive(INT16) => types.Int16
        case Primitive(CHAR) => types.Char
        case Primitive(INT32) => types.Int32
        case Primitive(INT64) => types.Int64
        case Primitive(FLOAT32) => types.Float32
        case Primitive(FLOAT64) => types.Float64
        case Primitive(FLOAT_BIG) => types.FloatBig
        case Primitive(INT_BIG) => types.IntBig
        case Primitive(BYTE_ARRAY) => types.ByteArray
        case Primitive(CHAR_ARRAY) => types.CharArray
        case Primitive(DATE) => types.Date

        // deprecated fields
        case Primitive(INT) => types.Int32
        case Primitive(BOOLEAN_PRIMITIVE) => types.Bool
        case Primitive(BYTE_PRIMITIVE) => types.Byte
        case Primitive(FLOAT_PRIMITIVE) => types.Float32
        case Primitive(DOUBLE_PRIMITIVE) => types.Float64
        case Primitive(SHORT_PRIMITIVE) => types.Int16
        case Primitive(LONG_PRIMITIVE) => types.Int64
        case Primitive(CHARACTER_PRIMITIVE) => types.Char
        case Primitive(BIG_DECIMAL_JAVA) => types.FloatBig
        case Primitive(BIG_INT_JAVA) => types.IntBig

        case Primitive(JODA_LOCAL_DATE) => types.Date
        case Primitive(JODA_LOCAL_DATETIME) => types.Date

        case Optional(OptionalType(Some(value))) => types.OptionType(ctx.toDomain[types.Type](value))

        case List(ListType(Some(value))) => types.ListType(ctx.toDomain[types.Type](value))

        case Record(RecordType(fields)) =>
          val mapped = fields.map {
            case protobuf.RecordField(Some(name), Some(fieldType)) =>
              val `type` = ctx.toDomain[types.Type](fieldType)
              types.RecordField(name, `type`)

            case _ => throw new IllegalStateException(s"Invalid value for record field (properties may not be None)")
          }

          types.RecordType(mapped)

        case Map(MapType(Some(value))) => types.MapType(ctx.toDomain[types.Type](value))

        case Enum(EnumType(options)) => types.EnumType(options.toSet)

        case unknownMessage => throw new IllegalStateException(s"Proto message with unknown type: ${unknownMessage.getClass}")
      }

    case msg: protobuf.Value =>

      import protobuf.Value.OneofValue._

      msg.oneofValue match {
        case NullValue(_) => types.NullValue
        case BooleanValue(bool) => types.PrimitiveValue(bool)
        case ByteValue(byte) => types.PrimitiveValue(byte.toByte)
        case ShortValue(short) => types.PrimitiveValue(short.toShort)
        case CharValue(char) => types.PrimitiveValue(char.toChar)
        case IntValue(int) => types.PrimitiveValue(int)
        case LongValue(long) => types.PrimitiveValue(long)
        case FloatValue(float) => types.PrimitiveValue(float)
        case DoubleValue(double) => types.PrimitiveValue(double)
        case StringValue(string) => types.PrimitiveValue(string)
        case BigDecimalScalaValue(bigdecimal) => types.PrimitiveValue(BigDecimal(bigdecimal))
        case BigDecimalJavaValue(bigdecimal) => types.PrimitiveValue(BigDecimal(bigdecimal).bigDecimal)
        case BigIntScalaValue(bigint) => types.PrimitiveValue(BigInt(bigint))
        case BigIntJavaValue(bigint) => types.PrimitiveValue(BigInt(bigint).bigInteger)
        case ByteArrayValue(byteArray) => types.PrimitiveValue(byteArray.toByteArray)
        case RecordValue(Record(fields)) => types.RecordValue(fields.mapValues(ctx.toDomain[types.Value]))

        // deprecated fields
        case ListValue(List(entries)) => types.ListValue(entries.map(ctx.toDomain[types.Value]).toList)
        case JodaDatetimeValue(date) =>
          val dateTime = ISODateTimeFormat.dateTime().parseDateTime(date)
          types.PrimitiveValue(dateTime.getMillis)
        case JodaLocaldateValue(date) =>
          val localDate = LocalDate.parse(date)
          types.PrimitiveValue(localDate.toDateTime(LocalTime.MIDNIGHT).getMillis)
        case JodaLocaldatetimeValue(date) =>
          val localDateTime = LocalDateTime.parse(date)
          types.PrimitiveValue(localDateTime.toDateTime.getMillis)

        case Empty => throw new IllegalStateException("Empty value cannot be deserialized")
      }
  }
}
