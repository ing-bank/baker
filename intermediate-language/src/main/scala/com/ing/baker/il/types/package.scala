package com.ing.baker.il

import scala.reflect.runtime.universe

package object types {

  type IngredientDescriptor = RecordField

  implicit class AsValueAddition(obj: Any) {
    def toValue: Value = Converters.toValue(obj)
  }

  val javaPrimitiveMappings: Map[Class[_], Class[_]] = Map(
    classOf[java.lang.Boolean]   -> java.lang.Boolean.TYPE,
    classOf[java.lang.Byte]      -> java.lang.Byte.TYPE,
    classOf[java.lang.Short]     -> java.lang.Short.TYPE,
    classOf[java.lang.Character] -> java.lang.Character.TYPE,
    classOf[java.lang.Integer]   -> java.lang.Integer.TYPE,
    classOf[java.lang.Long]      -> java.lang.Long.TYPE,
    classOf[java.lang.Float]     -> java.lang.Float.TYPE,
    classOf[java.lang.Double]    -> java.lang.Double.TYPE)

  val supportedPrimitiveClasses: Set[Class[_]] = Set(
    classOf[java.lang.String],
    classOf[java.math.BigDecimal],
    classOf[java.math.BigInteger],
    classOf[BigDecimal],
    classOf[BigInt]
  ) ++ javaPrimitiveMappings.keys ++ javaPrimitiveMappings.values

  // TYPES

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

        case _ => false
      }
    }
  }

  case class PrimitiveType(clazz: Class[_]) extends BType

  case class ListType(entryType: BType) extends BType

  case class OptionType(entryType: BType) extends BType

  case class EnumType(options: Set[String]) extends BType

  case class RecordType(fields: Seq[RecordField]) extends BType

  case class RecordField(name: String, `type`: BType)

  // VALUES

  sealed trait Value extends Serializable {

    def isNull: Boolean = this == NullValue

    def isInstanceOf(t: BType): Boolean = (t, this) match {
      case (PrimitiveType(clazz), v: PrimitiveValue)          => v.isAssignableTo(clazz)
      case (ListType(entryType), ListValue(entries))          => entries.forall(_.isInstanceOf(entryType))
      case (OptionType(_), NullValue)                         => true
      case (OptionType(entryType), v: Value)                  => v.isInstanceOf(entryType)
      case (EnumType(options), PrimitiveValue(value: String)) => options.contains(value)
      case (RecordType(entryTypes), RecordValue(entryValues)) => entryTypes.forall { f =>
        entryValues.get(f.name) match {
          case None        => false
          case Some(value) => value.isInstanceOf(f.`type`)
        }
      }
      case _ => false
    }

    def toJava(javaType: java.lang.reflect.Type) = Converters.toJava(this, javaType)

    def toJava[T : universe.TypeTag] = Converters.toJava[T](this)
  }

  /**
    * Indicates the absence of a value.
    *
    * null, void, none, empty, etc...
    *
    */
  case object NullValue extends Value

  // should inherit AnyVal
  case class PrimitiveValue(value: Any) extends Value {
    if (!isPrimitiveValue(value))
      throw new IllegalArgumentException(s"value is not supported: $value")

    def isAssignableTo(clazz: Class[_]) =
      (supportedPrimitiveClasses.contains(clazz) && clazz.isInstance(value)) ||
        (clazz.isPrimitive && javaPrimitiveMappings.get(value.getClass) == Some(clazz))
  }

  case class RecordValue(entries: Map[String, Value]) extends Value

  case class ListValue(entries: List[Value]) extends Value

  def isPrimitiveValue(obj: Any) = supportedPrimitiveClasses.exists(clazz => clazz.isInstance(obj))
}
