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
      case (PrimitiveType(clazzA), PrimitiveType(clazzB)) =>
        clazzB.equals(clazzA) ||
        javaPrimitiveMappings.get(clazzB).equals(Some(clazzA)) ||
          javaPrimitiveMappings.get(clazzA).equals(Some(clazzB))

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

case class PrimitiveType(clazz: Class[_]) extends Type

case class ListType(entryType: Type) extends Type

case class OptionType(entryType: Type) extends Type

case class EnumType(options: Set[String]) extends Type

case class RecordType(fields: Seq[RecordField]) extends Type

case class MapType(valueType: Type) extends Type

case class RecordField(name: String, `type`: Type)
