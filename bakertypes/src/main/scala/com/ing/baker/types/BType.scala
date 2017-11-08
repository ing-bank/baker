package com.ing.baker.types

sealed trait BType {

  def isAssignableFrom(other: BType): Boolean = {

    (this, other) match {
      case (PrimitiveType(clazzA), PrimitiveType(clazzB)) =>
        if (clazzA.isPrimitive)
          clazzB.equals(clazzA) || javaPrimitiveMappings.get(clazzB).equals(Some(clazzA))
        else
          clazzB.equals(clazzA)

      case (OptionType(entryTypeA), OptionType(entryTypeB)) =>
        entryTypeA.isAssignableFrom(entryTypeB)

      case (OptionType(entryType), otherType) =>
        entryType.isAssignableFrom(otherType)

      case (ListType(entryTypeA), ListType(entryTypeB)) =>
        entryTypeA.isAssignableFrom(entryTypeB)

      case (RecordType(entriesA), RecordType(entriesB)) =>
        val entriesMap: Map[String, BType] = entriesB.map(f => f.name -> f.`type`).toMap
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
}

case class PrimitiveType(clazz: Class[_]) extends BType

case class ListType(entryType: BType) extends BType

case class OptionType(entryType: BType) extends BType

case class EnumType(options: Set[String]) extends BType

case class RecordType(fields: Seq[RecordField]) extends BType

case class MapType(valueType: BType) extends BType

case class RecordField(name: String, `type`: BType)
