package com.ing.baker.runtime.actor.serialization.modules

import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf._
import com.ing.baker.types
import org.joda.time
import org.joda.time.format.ISODateTimeFormat
import org.joda.time.{LocalDate, LocalDateTime}

class TypesModule extends ProtoEventAdapterModule {

  private def createPrimitive(p: PrimitiveType) = protobuf.Type(Type.OneofType.Primitive(p))

  override def toProto(ctx: ProtoEventAdapterContext): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Boolean] =>
      createPrimitive(PrimitiveType.BOOLEAN_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Boolean.TYPE =>
      createPrimitive(PrimitiveType.BOOLEAN)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Byte] =>
      createPrimitive(PrimitiveType.BYTE_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Byte.TYPE =>
      createPrimitive(PrimitiveType.BYTE)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Short] =>
      createPrimitive(PrimitiveType.SHORT_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Short.TYPE =>
      createPrimitive(PrimitiveType.SHORT)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Character] =>
      createPrimitive(PrimitiveType.CHARACTER_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Character.TYPE =>
      createPrimitive(PrimitiveType.CHARACTER)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Integer] =>
      createPrimitive(PrimitiveType.INTEGER)
    case types.PrimitiveType(clazz) if clazz == java.lang.Integer.TYPE =>
      createPrimitive(PrimitiveType.INT)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Long] =>
      createPrimitive(PrimitiveType.LONG_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Long.TYPE =>
      createPrimitive(PrimitiveType.LONG)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Float] =>
      createPrimitive(PrimitiveType.FLOAT_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Float.TYPE =>
      createPrimitive(PrimitiveType.FLOAT)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Double] =>
      createPrimitive(PrimitiveType.DOUBLE_PRIMITIVE)
    case types.PrimitiveType(clazz) if clazz == java.lang.Double.TYPE =>
      createPrimitive(PrimitiveType.DOUBLE)
    case types.PrimitiveType(clazz) if clazz == classOf[java.lang.String] =>
      createPrimitive(PrimitiveType.STRING)
    case types.PrimitiveType(clazz) if clazz == classOf[BigDecimal] =>
      createPrimitive(PrimitiveType.BIG_DECIMAL_SCALA)
    case types.PrimitiveType(clazz) if clazz == classOf[java.math.BigDecimal] =>
      createPrimitive(PrimitiveType.BIG_DECIMAL_JAVA)
    case types.PrimitiveType(clazz) if clazz == classOf[BigInt] =>
      createPrimitive(PrimitiveType.BIG_INT_SCALA)
    case types.PrimitiveType(clazz) if clazz == classOf[java.math.BigInteger] =>
      createPrimitive(PrimitiveType.BIG_INT_JAVA)
    case types.PrimitiveType(clazz) if clazz == classOf[Array[Byte]] =>
      createPrimitive(PrimitiveType.BYTE_ARRAY)
    case types.PrimitiveType(clazz) if clazz == classOf[org.joda.time.DateTime] =>
      createPrimitive(PrimitiveType.JODA_DATETIME)
    case types.PrimitiveType(clazz) if clazz == classOf[org.joda.time.LocalDate] =>
      createPrimitive(PrimitiveType.JODA_LOCAL_DATE)
    case types.PrimitiveType(clazz) if clazz == classOf[org.joda.time.LocalDateTime] =>
      createPrimitive(PrimitiveType.JODA_LOCAL_DATETIME)

    case types.OptionType(entryType) =>
      val entryProto = ctx.toProtoType[protobuf.Type](entryType)
      protobuf.Type(Type.OneofType.Optional(OptionalType(Some(entryProto))))

    case types.ListType(entryType) =>
      val entryProto = ctx.toProtoType[protobuf.Type](entryType)
      protobuf.Type(Type.OneofType.List(ListType(Some(entryProto))))

    case types.RecordType(fields) =>

      val protoFields = fields.map { f =>
        val protoType = ctx.toProtoType[protobuf.Type](f.`type`)
        protobuf.RecordField(Some(f.name), Some(protoType))
      }

      protobuf.Type(Type.OneofType.Record(RecordType(protoFields)))

    case types.MapType(valueType) =>
      val valueProto = ctx.toProtoType[protobuf.Type](valueType)
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
      case types.PrimitiveValue(value: org.joda.time.DateTime) => protobuf.Value(protobuf.Value.OneofValue.JodaDatetimeValue(ISODateTimeFormat.dateTime().print(value)))
      case types.PrimitiveValue(value: org.joda.time.LocalDate) => protobuf.Value(protobuf.Value.OneofValue.JodaLocaldateValue(value.toString))
      case types.PrimitiveValue(value: org.joda.time.LocalDateTime) => protobuf.Value(protobuf.Value.OneofValue.JodaLocaldatetimeValue(value.toString))
      case types.PrimitiveValue(value) => throw new IllegalStateException(s"Unknown primitive value of type: ${value.getClass}")
      case types.RecordValue(entries) => protobuf.Value(protobuf.Value.OneofValue.RecordValue(protobuf.Record(entries.mapValues(ctx.toProtoType[protobuf.Value]))))
      case types.ListValue(entries) => protobuf.Value(protobuf.Value.OneofValue.ListValue(protobuf.List(entries.map(ctx.toProtoType[protobuf.Value]))))
    }

  }

  override def toDomain(ctx: ProtoEventAdapterContext): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {

    case msg: protobuf.Type =>

      import Type.OneofType

      msg.`oneofType` match {
        case OneofType.Primitive(PrimitiveType.BOOLEAN) => types.PrimitiveType(classOf[Boolean])
        case OneofType.Primitive(PrimitiveType.BOOLEAN_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Boolean])
        case OneofType.Primitive(PrimitiveType.BYTE) => types.PrimitiveType(classOf[Byte])
        case OneofType.Primitive(PrimitiveType.BYTE_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Byte])
        case OneofType.Primitive(PrimitiveType.SHORT) => types.PrimitiveType(classOf[Short])
        case OneofType.Primitive(PrimitiveType.SHORT_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Short])
        case OneofType.Primitive(PrimitiveType.CHARACTER_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Character])
        case OneofType.Primitive(PrimitiveType.CHARACTER) => types.PrimitiveType(classOf[Char])
        case OneofType.Primitive(PrimitiveType.INTEGER) => types.PrimitiveType(classOf[Integer])
        case OneofType.Primitive(PrimitiveType.INT) => types.PrimitiveType(classOf[Int])
        case OneofType.Primitive(PrimitiveType.LONG) => types.PrimitiveType(classOf[Long])
        case OneofType.Primitive(PrimitiveType.LONG_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Long])
        case OneofType.Primitive(PrimitiveType.FLOAT) => types.PrimitiveType(classOf[Float])
        case OneofType.Primitive(PrimitiveType.FLOAT_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Float])
        case OneofType.Primitive(PrimitiveType.DOUBLE) => types.PrimitiveType(classOf[Double])
        case OneofType.Primitive(PrimitiveType.DOUBLE_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Double])
        case OneofType.Primitive(PrimitiveType.STRING) => types.PrimitiveType(classOf[String])
        case OneofType.Primitive(PrimitiveType.BIG_DECIMAL_SCALA) => types.PrimitiveType(classOf[BigDecimal])
        case OneofType.Primitive(PrimitiveType.BIG_DECIMAL_JAVA) => types.PrimitiveType(classOf[java.math.BigDecimal])
        case OneofType.Primitive(PrimitiveType.BIG_INT_SCALA) => types.PrimitiveType(classOf[BigInt])
        case OneofType.Primitive(PrimitiveType.BIG_INT_JAVA) => types.PrimitiveType(classOf[java.math.BigInteger])
        case OneofType.Primitive(PrimitiveType.BYTE_ARRAY) => types.PrimitiveType(classOf[Array[Byte]])
        case OneofType.Primitive(PrimitiveType.JODA_DATETIME) => types.PrimitiveType(classOf[time.DateTime])
        case OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATE) => types.PrimitiveType(classOf[time.LocalDate])
        case OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATETIME) => types.PrimitiveType(classOf[time.LocalDateTime])

        case OneofType.Optional(OptionalType(Some(value))) => types.OptionType(ctx.toDomainType[types.Type](value))

        case OneofType.List(ListType(Some(value))) => types.ListType(ctx.toDomainType[types.Type](value))

        case OneofType.Record(RecordType(fields)) =>
          val mapped = fields.map {
            case protobuf.RecordField(Some(name), Some(fieldType)) =>
              val `type` = ctx.toDomainType[types.Type](fieldType)
              types.RecordField(name, `type`)

            case _ => throw new IllegalStateException(s"Invalid value for record field (properties may not be None)")
          }

          types.RecordType(mapped)

        case OneofType.Map(MapType(Some(value))) => types.MapType(ctx.toDomainType[types.Type](value))

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
        case OneofValue.JodaDatetimeValue(date) => types.PrimitiveValue(ISODateTimeFormat.dateTime().parseDateTime(date))
        case OneofValue.JodaLocaldateValue(date) => types.PrimitiveValue(LocalDate.parse(date))
        case OneofValue.JodaLocaldatetimeValue(date) => types.PrimitiveValue(LocalDateTime.parse(date))
        case OneofValue.RecordValue(Record(fields)) => types.RecordValue(fields.mapValues(ctx.toDomainType[types.Value]))
        case OneofValue.ListValue(List(entries)) => types.ListValue(entries.map(ctx.toDomainType[types.Value]).toList)
        case OneofValue.Empty => throw new IllegalStateException("Empty value cannot be deserialized")
      }
  }
}
