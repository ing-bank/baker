package com.ing.baker

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
    classOf[BigInt],
    classOf[org.joda.time.DateTime],
    classOf[org.joda.time.LocalDate],
    classOf[org.joda.time.LocalDateTime],
    classOf[Array[Byte]]
  ) ++ javaPrimitiveMappings.keys ++ javaPrimitiveMappings.values

  // TYPES

  def isPrimitiveValue(obj: Any) = supportedPrimitiveClasses.exists(clazz => clazz.isInstance(obj))
}
