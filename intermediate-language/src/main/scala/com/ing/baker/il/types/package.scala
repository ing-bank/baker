package com.ing.baker.il

import scala.reflect.runtime.universe

package object types {

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

  sealed trait BType

  case class PrimitiveType(clazz: Class[_]) extends BType

  case class ListType(entryType: BType) extends BType

  case class OptionType(entryType: BType) extends BType

  case class EnumType(options: Set[String]) extends BType

  case class RecordType(fields: Seq[IngredientDescriptor]) extends BType

  // VALUES

  sealed trait Value {

    def isInstanceOf(t: BType): Boolean = ???
    def toJava(javaType: java.lang.reflect.Type) = Converters.toJava(this, javaType)
    def toJava[T : universe.TypeTag] = Converters.toJava[T](this)
  }

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
