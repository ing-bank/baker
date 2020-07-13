package com.ing.baker.types

//object Type {
//
//  private val extractSquareBracketsValue = "^[^]]+[(.*]$".r
//
//  private def outerSquareBracketsIn(typeDef: String): Boolean = typeDef.endsWith("]")
//
//  private def extractSquareBracketsType(typeDef: String): (String, String) = ???
//
//  private def extractEnumOptions(typeDef: String): Set[String] = ???
//
//  private def extractRecordFields(typ)
//
//  def fromString(s: String) : Either[String, Type] = s match {
//    case "Bool" => Right(Bool)
//    case "Byte" => Right(Byte)
//    case "Char" => Right(Char)
//    case "Date" => Right(Date)
//    case "Int16" => Right(Int16)
//    case "Int32" => Right(Int32)
//    case "Int64" => Right(Int64)
//    case "IntBig" => Right(IntBig)
//    case "Float32" => Right(Float32)
//    case "Float64" => Right(Float64)
//    case "FloatBig" => Right(FloatBig)
//
//    case typeDefinition: String if outerSquareBracketsIn(typeDefinition) =>
//      val (outerTypeDef, innerTypeDef) = extractSquareBracketsType(typeDefinition)
//      for {
//        innerType <- fromString(innerTypeDef)
//        outerType <- outerTypeDef match {
//          case "OptionType" => Right(OptionType(innerType))
//          case "ListType" => Right(ListType(innerType))
//          case "MapType" => Right(MapType(innerType))
//          case _ => Left(s"Type $outerTypeDef is unknown")
//        }
//      } yield outerType
//
//    case typeDefinition: String if typeDefinition.startsWith("EnumType") =>
//      Right(EnumType(extractEnumOptions(typeDefinition)))
//
//    case typeDefinition: String if typeDefinition.startsWith("RecordType") =>
//      Right(RecordType(extractRecordFields(typeDefinition)))
//
//    case _ => Left(s"Can't parse type $s")
//  }
//}

sealed trait Type {

  /**
    * Checks if an instance of other is also an instance of this type.
    *
    * @param other
    * @return
    */
  def isAssignableFrom(other: Type): Boolean = {

    (this, other) match {

      case (a, b) if a == b => true

      case (Bool, Bool) => true
      case (Byte, Byte) => true
      case (Char, Char) => true
      case (Date, Date) => true
      case (Int16, Int16) => true
      case (Int32, Int32 | Int16) => true
      case (Int64, Int64 | Int32 | Int16) => true
      case (IntBig, IntBig | Int64 | Int32 | Int16) => true
      case (Float32, Float32) => true
      case (Float64, Float64 | Float32) => true
      case (FloatBig, FloatBig | Float32 | Float64) => true

      case (OptionType(entryTypeA), OptionType(entryTypeB)) => entryTypeA.isAssignableFrom(entryTypeB)

      case (OptionType(entryType), otherType) => entryType.isAssignableFrom(otherType)

      case (ListType(entryTypeA), ListType(entryTypeB)) => entryTypeA.isAssignableFrom(entryTypeB)

      case (EnumType(optionsA), EnumType(optionsB)) => optionsB.subsetOf(optionsA)

      case (MapType(valueTypeA), MapType(valueTypeB)) => valueTypeA.isAssignableFrom(valueTypeB)

      case (RecordType(entriesA), RecordType(entriesB)) =>
        val entriesMap: Map[String, Type] = entriesB.map(f => f.name -> f.`type`).toMap
        entriesA.forall { f =>
          entriesMap.get(f.name) match {
            case None            => false
            case Some(fieldType) => f.`type`.isAssignableFrom(fieldType)
          }
        }

      case _ => false
    }
  }

  def isPrimitive: Boolean = isInstanceOf[PrimitiveType]
  def isOption: Boolean = isInstanceOf[OptionType]
  def isList: Boolean = isInstanceOf[ListType]
  def isEnum: Boolean = isInstanceOf[EnumType]
  def isMap: Boolean = isInstanceOf[MapType]
  def isRecord: Boolean = isInstanceOf[RecordType]

  override def hashCode(): Int = {
    val p1 = 31
    val p2 = 11
    this match {
      case ListType(entryType) =>
        p1 * 1 + entryType.hashCode()
        //p * 1 + (p * 17) == p * 6 + (p * 12)
      case OptionType(entryType) =>
        p1 * 2 + entryType.hashCode()
      case EnumType(options) =>
        p1 * 3 + options.hashCode()
      case RecordType(fields) =>
        p1 * 5 + fields.hashCode()
      case MapType(valueType) =>
        p1 * 6 + valueType.hashCode()
      case Bool => p2 * 7
      case Byte => p2 * 8
      case Char => p2 * 9
      case Int16 => p2 * 10
      case Int32 => p2 * 11
      case Int64 => p2 * 12
      case IntBig => p2 * 13
      case Float32 => p2 * 14
      case Float64 => p2 * 15
      case FloatBig => p2 * 16
      case ByteArray => p2 * 17
      case CharArray => p2 * 18
      case Date => p2 * 19
    }
  }
}

case class ListType(entryType: Type) extends Type {
  override def toString: String = s"List[$entryType]"
}

case class OptionType(entryType: Type) extends Type {

  override def toString: String = s"Option[$entryType]"
}

case class EnumType(options: Set[String]) extends Type {

  override def toString: String = s"Enum(${options.mkString(" | ")})"
}

case class RecordField(name: String, `type`: Type) {

  override def toString: String = s"$name: ${`type`}"

  override def hashCode(): Int = {
    val p = 23
    val nameHash = p * 4 + name.hashCode()
    p * nameHash + `type`.hashCode()
  }
}

case class RecordType(fields: Seq[RecordField]) extends Type {

  override def toString: String = s"Record(${fields.mkString(", ")})"
}

case class MapType(valueType: Type) extends Type {

  override def toString: String = s"Map[$valueType]"
}

sealed trait PrimitiveType extends Type

/**
  * Boolean (1 bit)
  */
case object Bool extends PrimitiveType{
  override def toString = "Bool"
}

/**
  * Signed 8 bit integer
  */
case object Byte extends PrimitiveType {
  override def toString = "Byte"
}

/**
  * Character (Unsigned 16 bit integer)
  */
case object Char extends PrimitiveType {
  override def toString = "Char"
}

/**
  * Signed 16 bit integer
  */
case object Int16 extends PrimitiveType {
  override def toString = "Int16"
}

/**
  * Signed 32 bit integer
  */
case object Int32 extends PrimitiveType {
  override def toString = "Int32"
}

/**
  * Signed 64 bit integer
  */
case object Int64 extends PrimitiveType {
  override def toString = "Int64"
}

/**
  * Integer of arbitrary precision
  */
case object IntBig extends PrimitiveType {
  override def toString = "IntBig"
}

/**
  * Signed 32 bit floating point
  */
case object Float32 extends PrimitiveType {
  override def toString = "Float32"
}

/**
  * Signed 64 bit floating point
  */
case object Float64 extends PrimitiveType {
  override def toString = "Float64"
}

/**
  * Floating point with arbitrary precision
  */
case object FloatBig extends PrimitiveType {
  override def toString = "FloatBig"
}

/**
  * Byte array
  */
case object ByteArray extends PrimitiveType {
  override def toString = "ByteArray"
}

/**
  * Character array
  */
case object CharArray extends PrimitiveType {
  override def toString = "CharArray"
}

/**
  * Date is technically equal to Int64
  *
  * The definition we use is:
  *
  * A UTC date in the ISO-8601 calendar system with millisecond precision
  */
case object Date extends PrimitiveType {
  override def toString = "Date"
}

