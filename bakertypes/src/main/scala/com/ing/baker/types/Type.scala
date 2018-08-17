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

trait PrimitiveType extends Type

// boolean
case object Bool extends PrimitiveType
// byte
case object Int8 extends PrimitiveType
// char, unsigned 16 bit integer
case object UInt16 extends PrimitiveType
// short or char
case object Int16 extends PrimitiveType
// int
case object Int32 extends PrimitiveType
// long
case object Int64 extends PrimitiveType
// BigInteger
case object IntBig extends PrimitiveType
// float
case object Float32 extends PrimitiveType
// double
case object Float64 extends PrimitiveType
// BigNumber
case object FloatBig extends PrimitiveType

// byte array
case object ByteArray extends PrimitiveType

// string
case object CharArray extends PrimitiveType

