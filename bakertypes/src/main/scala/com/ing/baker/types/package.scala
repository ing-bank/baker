package com.ing.baker

package object types {

  import org.joda.time.format.DateTimeFormatter
  import org.joda.time.format.ISODateTimeFormat

  val isoDateTimeFormatter: DateTimeFormatter = ISODateTimeFormat.dateTime

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

  val primitiveMappings: Map[Class[_], Type] = Map(
    classOf[java.lang.Boolean]    -> types.Bool,
    java.lang.Boolean.TYPE        -> types.Bool,
    classOf[java.lang.Byte]       -> types.Byte,
    java.lang.Byte.TYPE           -> types.Byte,
    classOf[java.lang.Short]      -> types.Int16,
    java.lang.Short.TYPE          -> types.Int16,
    classOf[java.lang.Character]  -> types.UInt16,
    java.lang.Character.TYPE      -> types.UInt16,
    classOf[java.lang.Integer]    -> types.Int32,
    java.lang.Integer.TYPE        -> types.Int32,
    classOf[java.lang.Long]       -> types.Int64,
    java.lang.Long.TYPE           -> types.Int64,
    classOf[java.lang.Float]      -> types.Float32,
    java.lang.Float.TYPE          -> types.Float32,
    classOf[java.lang.Double]     -> types.Float64,
    java.lang.Double.TYPE         -> types.Float64,
    classOf[java.math.BigInteger] -> types.IntBig,
    classOf[BigInt]               -> types.IntBig,
    classOf[java.math.BigDecimal] -> types.FloatBig,
    classOf[BigDecimal]           -> types.FloatBig,
    classOf[Array[Byte]]          -> types.ByteArray,
    classOf[String]               -> types.CharArray)

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
