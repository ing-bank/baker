package com.ing.baker.runtime.actortyped.serialization.protomappings

import cats.implicits._
import com.ing.baker.types
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf._
import Type.OneofType._
import PrimitiveType._
import com.ing.baker.runtime.actor.protobuf.Type.OneofType

import scala.util.{Failure, Success, Try}

class BakerTypesMapping extends ProtoMap[types.Type, protobuf.Type] {

  val companion = protobuf.Type

  private def createPrimitive(p: PrimitiveType) =
    protobuf.Type(protobuf.Type.OneofType.Primitive(p))

  def toProto(t: types.Type): protobuf.Type = t match {
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

    case types.Date =>
      createPrimitive(PrimitiveType.DATE)

    case types.OptionType(entryType) =>
      val entryProto = toProto(entryType)
      protobuf.Type(protobuf.Type.OneofType.Optional(protobuf.OptionalType(Some(entryProto))))

    case types.ListType(entryType) =>
      val entryProto = toProto(entryType)
      protobuf.Type(protobuf.Type.OneofType.List(protobuf.ListType(Some(entryProto))))

    case types.RecordType(fields) =>

      val protoFields = fields.map { f =>
        val protoType = toProto(f.`type`)
        protobuf.RecordField(Some(f.name), Some(protoType))
      }

      protobuf.Type(protobuf.Type.OneofType.Record(protobuf.RecordType(protoFields)))

    case types.MapType(valueType) =>
      val valueProto = toProto(valueType)
      protobuf.Type(protobuf.Type.OneofType.Map(protobuf.MapType(Some(valueProto))))

    case types.EnumType(options) =>
      protobuf.Type(protobuf.Type.OneofType.Enum(protobuf.EnumType(options.toSeq)))
  }

  def fromProto(message: protobuf.Type): Try[types.Type] = {
    message.`oneofType` match {

      case Primitive(BOOL) => Success(types.Bool)
      case Primitive(BYTE) => Success(types.Byte)
      case Primitive(INT16) => Success(types.Int16)
      case Primitive(CHAR) => Success(types.Char)
      case Primitive(INT32) => Success(types.Int32)
      case Primitive(INT64) => Success(types.Int64)
      case Primitive(FLOAT32) => Success(types.Float32)
      case Primitive(FLOAT64) => Success(types.Float64)
      case Primitive(FLOAT_BIG) => Success(types.FloatBig)
      case Primitive(INT_BIG) => Success(types.IntBig)
      case Primitive(BYTE_ARRAY) => Success(types.ByteArray)
      case Primitive(CHAR_ARRAY) => Success(types.CharArray)
      case Primitive(DATE) => Success(types.Date)

        // deprecated fields
      case Primitive(INT) => Success(types.Int32)
      case Primitive(BOOLEAN_PRIMITIVE) => Success(types.Bool)
      case Primitive(BYTE_PRIMITIVE) => Success(types.Byte)
      case Primitive(FLOAT_PRIMITIVE) => Success(types.Float32)
      case Primitive(DOUBLE_PRIMITIVE) => Success(types.Float64)
      case Primitive(SHORT_PRIMITIVE) => Success(types.Int16)
      case Primitive(LONG_PRIMITIVE) => Success(types.Int64)
      case Primitive(CHARACTER_PRIMITIVE) => Success(types.Char)
      case Primitive(BIG_DECIMAL_JAVA) => Success(types.FloatBig)
      case Primitive(BIG_INT_JAVA) => Success(types.IntBig)

      case Primitive(JODA_LOCAL_DATE) => Success(types.Date)
      case Primitive(JODA_LOCAL_DATETIME) => Success(types.Date)

      case OneofType.Optional(OptionalType(Some(value))) =>
        fromProto(value).map(types.OptionType)

      case OneofType.List(ListType(Some(value))) =>
        fromProto(value).map(types.ListType)

      case OneofType.Record(RecordType(fields)) =>
        val record = fields.toList.traverse[Try, types.RecordField] {
          case protobuf.RecordField(Some(name), Some(fieldType)) =>
            fromProto(fieldType).map(types.RecordField(name, _))
          case _ =>
            Failure(new IllegalStateException(s"Invalid value for record field (properties may not be None)"))
        }

        record.map(types.RecordType)

      case OneofType.Map(MapType(Some(value))) =>
        fromProto(value).map(types.MapType)

      case OneofType.Enum(EnumType(options)) =>
        Success(types.EnumType(options.toSet))

      case unknownMessage =>
        Failure(new IllegalStateException(s"Proto message with unknown type: ${unknownMessage.getClass}"))
    }
  }

}
