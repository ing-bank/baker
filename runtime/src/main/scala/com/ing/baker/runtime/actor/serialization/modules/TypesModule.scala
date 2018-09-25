package com.ing.baker.runtime.actor.serialization.modules

import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf._
import com.ing.baker.types
import org.joda.time.format.ISODateTimeFormat
import org.joda.time.{LocalDate, LocalDateTime, LocalTime}

class TypesModule extends ProtoEventAdapterModule {

  private def createPrimitive(p: PrimitiveType) = protobuf.Type(Type.OneofType.Primitive(p))

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {

    case types.Bool =>
      createPrimitive(PrimitiveType.BOOL)
    case types.Byte =>
      createPrimitive(PrimitiveType.BYTE)
    case types.Int16 =>
      createPrimitive(PrimitiveType.INT16)
    case types.Char =>
      createPrimitive(PrimitiveType.CHAR)
    case types.Int32 =>
      createPrimitive(PrimitiveType.INT)
    case types.Int64 =>
      createPrimitive(PrimitiveType.INT64)
    case types.Float32 =>
      createPrimitive(PrimitiveType.FLOAT32)
    case types.Float64 =>
      createPrimitive(PrimitiveType.FLOAT64)
    case types.CharArray =>
      createPrimitive(PrimitiveType.CHAR_ARRAY)
    case types.FloatBig =>
      createPrimitive(PrimitiveType.FLOAT_BIG)
    case types.IntBig =>
      createPrimitive(PrimitiveType.INT_BIG)
    case types.ByteArray =>
      createPrimitive(PrimitiveType.BYTE_ARRAY)

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

    case v: types.Value => v match {
      case types.NullValue => protobuf.Value(protobuf.Value.OneofValue.NullValue(true))
      case types.PrimitiveValue(value: Boolean) => protobuf.Value(protobuf.Value.OneofValue.BooleanValue(value))
      case types.PrimitiveValue(value: Byte) => protobuf.Value(protobuf.Value.OneofValue.ByteValue(value))
      case types.PrimitiveValue(value: Short) => protobuf.Value(protobuf.Value.OneofValue.ShortValue(value))
      case types.PrimitiveValue(value: Char) => protobuf.Value(protobuf.Value.OneofValue.CharValue(value))
      case types.PrimitiveValue(value: Int) => protobuf.Value(protobuf.Value.OneofValue.IntValue(value))
      case types.PrimitiveValue(value: Long) => protobuf.Value(protobuf.Value.OneofValue.LongValue(value))
      case types.PrimitiveValue(value: Float) => protobuf.Value(protobuf.Value.OneofValue.FloatValue(value))
      case types.PrimitiveValue(value: Double) => protobuf.Value(protobuf.Value.OneofValue.DoubleValue(value))
      case types.PrimitiveValue(value: String) => protobuf.Value(protobuf.Value.OneofValue.StringValue(value))
      case types.PrimitiveValue(value: BigDecimal) => protobuf.Value(protobuf.Value.OneofValue.BigDecimalScalaValue(value.toString()))
      case types.PrimitiveValue(value: java.math.BigDecimal) => protobuf.Value(protobuf.Value.OneofValue.BigDecimalJavaValue(BigDecimal(value).toString()))
      case types.PrimitiveValue(value: BigInt) => protobuf.Value(protobuf.Value.OneofValue.BigIntScalaValue(value.toString()))
      case types.PrimitiveValue(value: java.math.BigInteger) => protobuf.Value(protobuf.Value.OneofValue.BigIntJavaValue(BigInt(value).toString()))
      case types.PrimitiveValue(value: Array[Byte]) => protobuf.Value(protobuf.Value.OneofValue.ByteArrayValue(ByteString.copyFrom(value)))
      case types.PrimitiveValue(value) => throw new IllegalStateException(s"Unknown primitive value of type: ${value.getClass}")
      case types.RecordValue(entries) => protobuf.Value(protobuf.Value.OneofValue.RecordValue(protobuf.Record(entries.mapValues(ctx.toProto[protobuf.Value]))))
      case types.ListValue(entries) => protobuf.Value(protobuf.Value.OneofValue.ListValue(protobuf.List(entries.map(ctx.toProto[protobuf.Value]))))
    }

  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {

    case msg: protobuf.Type =>

      import Type.OneofType

      msg.`oneofType` match {
        case OneofType.Primitive(PrimitiveType.BOOL) => types.Bool
        case OneofType.Primitive(PrimitiveType.BYTE) => types.Byte
        case OneofType.Primitive(PrimitiveType.INT16) => types.Int16
        case OneofType.Primitive(PrimitiveType.CHAR) => types.Char
        case OneofType.Primitive(PrimitiveType.INT32) => types.Int32
        case OneofType.Primitive(PrimitiveType.INT64) => types.Int64
        case OneofType.Primitive(PrimitiveType.FLOAT32) => types.Float32
        case OneofType.Primitive(PrimitiveType.FLOAT64) => types.Float64
        case OneofType.Primitive(PrimitiveType.FLOAT_BIG) => types.FloatBig
        case OneofType.Primitive(PrimitiveType.INT_BIG) => types.IntBig
        case OneofType.Primitive(PrimitiveType.BYTE_ARRAY) => types.ByteArray
        case OneofType.Primitive(PrimitiveType.CHAR_ARRAY) => types.CharArray
        case OneofType.Primitive(PrimitiveType.INT) => types.Int32


        // deprecated fields
        case OneofType.Primitive(PrimitiveType.BOOLEAN_PRIMITIVE) => types.Bool
        case OneofType.Primitive(PrimitiveType.BYTE_PRIMITIVE) => types.Byte
        case OneofType.Primitive(PrimitiveType.FLOAT_PRIMITIVE) => types.Float32
        case OneofType.Primitive(PrimitiveType.DOUBLE_PRIMITIVE) => types.Float64
        case OneofType.Primitive(PrimitiveType.SHORT_PRIMITIVE) => types.Int16
        case OneofType.Primitive(PrimitiveType.LONG_PRIMITIVE) => types.Int64
        case OneofType.Primitive(PrimitiveType.CHARACTER_PRIMITIVE) => types.Char
        case OneofType.Primitive(PrimitiveType.BIG_DECIMAL_JAVA) => types.FloatBig
        case OneofType.Primitive(PrimitiveType.BIG_INT_JAVA) => types.IntBig

        case OneofType.Primitive(PrimitiveType.JODA_DATETIME) => types.Int64
        case OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATE) => types.Int64
        case OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATETIME) => types.Int64

        case OneofType.Optional(OptionalType(Some(value))) => types.OptionType(ctx.toDomain[types.Type](value))

        case OneofType.List(ListType(Some(value))) => types.ListType(ctx.toDomain[types.Type](value))

        case OneofType.Record(RecordType(fields)) =>
          val mapped = fields.map {
            case protobuf.RecordField(Some(name), Some(fieldType)) =>
              val `type` = ctx.toDomain[types.Type](fieldType)
              types.RecordField(name, `type`)

            case _ => throw new IllegalStateException(s"Invalid value for record field (properties may not be None)")
          }

          types.RecordType(mapped)

        case OneofType.Map(MapType(Some(value))) => types.MapType(ctx.toDomain[types.Type](value))

        case OneofType.Enum(EnumType(options)) => types.EnumType(options.toSet)

        case unknownMessage => throw new IllegalStateException(s"Proto message with unknown type: ${unknownMessage.getClass}")
      }

    case msg: protobuf.Value =>

      import protobuf.Value.OneofValue

      msg.oneofValue match {
        case OneofValue.NullValue(_) => types.NullValue
        case OneofValue.BooleanValue(bool) => types.PrimitiveValue(bool)
        case OneofValue.ByteValue(byte) => types.PrimitiveValue(byte.toByte)
        case OneofValue.ShortValue(short) => types.PrimitiveValue(short.toShort)
        case OneofValue.CharValue(char) => types.PrimitiveValue(char.toChar)
        case OneofValue.IntValue(int) => types.PrimitiveValue(int)
        case OneofValue.LongValue(long) => types.PrimitiveValue(long)
        case OneofValue.FloatValue(float) => types.PrimitiveValue(float)
        case OneofValue.DoubleValue(double) => types.PrimitiveValue(double)
        case OneofValue.StringValue(string) => types.PrimitiveValue(string)
        case OneofValue.BigDecimalScalaValue(bigdecimal) => types.PrimitiveValue(BigDecimal(bigdecimal))
        case OneofValue.BigDecimalJavaValue(bigdecimal) => types.PrimitiveValue(BigDecimal(bigdecimal).bigDecimal)
        case OneofValue.BigIntScalaValue(bigint) => types.PrimitiveValue(BigInt(bigint))
        case OneofValue.BigIntJavaValue(bigint) => types.PrimitiveValue(BigInt(bigint).bigInteger)
        case OneofValue.ByteArrayValue(byteArray) => types.PrimitiveValue(byteArray.toByteArray)
        case OneofValue.RecordValue(Record(fields)) => types.RecordValue(fields.mapValues(ctx.toDomain[types.Value]))

        // deprecated fields
        case OneofValue.ListValue(List(entries)) => types.ListValue(entries.map(ctx.toDomain[types.Value]).toList)
        case OneofValue.JodaDatetimeValue(date) =>
          val dateTime = ISODateTimeFormat.dateTime().parseDateTime(date)
          types.PrimitiveValue(dateTime.getMillis)
        case OneofValue.JodaLocaldateValue(date) =>
          val localDate = LocalDate.parse(date)
          types.PrimitiveValue(localDate.toDateTime(LocalTime.MIDNIGHT).getMillis)
        case OneofValue.JodaLocaldatetimeValue(date) =>
          val localDateTime = LocalDateTime.parse(date)
          types.PrimitiveValue(localDateTime.toDateTime.getMillis)

        case OneofValue.Empty => throw new IllegalStateException("Empty value cannot be deserialized")
      }
  }
}
