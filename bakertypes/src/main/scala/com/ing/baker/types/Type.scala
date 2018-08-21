package com.ing.baker.types

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

      case (Int64, Int32) => true
      case (Float64, Float32) => true
      case (IntBig, Int32 | Int64) => true
      case (FloatBig, Float32 | Float64) => true

      case (OptionType(entryTypeA), OptionType(entryTypeB)) =>
        entryTypeA.isAssignableFrom(entryTypeB)

      case (OptionType(entryType), otherType) =>
        entryType.isAssignableFrom(otherType)

      case (ListType(entryTypeA), ListType(entryTypeB)) =>
        entryTypeA.isAssignableFrom(entryTypeB)

      case (RecordType(entriesA), RecordType(entriesB)) =>
        val entriesMap: Map[String, Type] = entriesB.map(f => f.name -> f.`type`).toMap
        entriesA.forall { f =>
          entriesMap.get(f.name) match {
            case None            => false
            case Some(fieldType) => f.`type`.isAssignableFrom(fieldType)
          }
        }
      case (EnumType(optionsA), EnumType(optionsB)) =>
        optionsB.subsetOf(optionsA)

      case (MapType(valueTypeA), MapType(valueTypeB)) =>
        valueTypeA.isAssignableFrom(valueTypeB)

      case _ => false
    }
  }

  def isPrimitive: Boolean = isInstanceOf[PrimitiveType]
  def isOption: Boolean = isInstanceOf[OptionType]
  def isList: Boolean = isInstanceOf[ListType]
  def isEnum: Boolean = isInstanceOf[EnumType]
  def isMap: Boolean = isInstanceOf[MapType]
  def isRecord: Boolean = isInstanceOf[RecordType]
}

case class ListType(entryType: Type) extends Type

case class OptionType(entryType: Type) extends Type

case class EnumType(options: Set[String]) extends Type

case class RecordType(fields: Seq[RecordField]) extends Type

case class MapType(valueType: Type) extends Type

case class RecordField(name: String, `type`: Type)

case class SingletonType(value: Value)

trait PrimitiveType extends Type

/**
  * Boolean (1 bit)
  */
case object Bool extends PrimitiveType

/**
  * Signed 8 bit integer
  */
case object Byte extends PrimitiveType

/**
  * Character (Unsigned 16 bit integer)
  */
case object Char extends PrimitiveType

/**
  * Signed 16 bit integer
  */
case object Int16 extends PrimitiveType

/**
  * Signed 32 bit integer
  */
case object Int32 extends PrimitiveType

/**
  * Signed 64 bit integer
  */
case object Int64 extends PrimitiveType

/**
  * Integer of arbitrary precision
  */
case object IntBig extends PrimitiveType

/**
  * Signed 32 bit floating point
  */
case object Float32 extends PrimitiveType

/**
  * Signed 64 bit floating point
  */
case object Float64 extends PrimitiveType

/**
  * Floating point with arbitrary precision
  */
case object FloatBig extends PrimitiveType

/**
  * Byte array
  */
case object ByteArray extends PrimitiveType

/**
  * Character array
  */
case object CharArray extends PrimitiveType

