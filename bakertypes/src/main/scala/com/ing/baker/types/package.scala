package com.ing.baker

import java.lang.reflect.ParameterizedType

import scala.reflect.runtime.universe

package object types {

  val mirror: universe.Mirror = universe.runtimeMirror(classOf[Value].getClassLoader)

  /**
    * Attempts to return the 'raw' or base class of a type. For example:
    *
    * String           -> String
    * List[String]     -> List
    * Map[String, Int] -> Map
    */
  def getBaseClass(javaType: java.lang.reflect.Type): Class[_] = javaType match {
    case c: Class[_] => c
    case t: ParameterizedType => getBaseClass(t.getRawType)
    case t @ _ => throw new IllegalArgumentException(s"Unsupported type: $javaType")
  }

  def getTypeParameter(javaType: java.lang.reflect.Type, index: Int): java.lang.reflect.Type = {
    javaType.asInstanceOf[ParameterizedType].getActualTypeArguments()(index)
  }

  def isAssignableToBaseClass(javaType: java.lang.reflect.Type, base: Class[_]) = base.isAssignableFrom(getBaseClass(javaType))

  def createJavaType(paramType: universe.Type): java.lang.reflect.Type = {
    val typeConstructor = mirror.runtimeClass(paramType)
    val innerTypes = paramType.typeArgs.map(createJavaType).toArray

    if (innerTypes.isEmpty) {
      typeConstructor
    } else {
      new java.lang.reflect.ParameterizedType {
        override def getRawType: java.lang.reflect.Type = typeConstructor
        override def getActualTypeArguments: Array[java.lang.reflect.Type] = innerTypes
        override def getOwnerType: java.lang.reflect.Type = null
        override def toString() = s"ParameterizedType: $typeConstructor[${getActualTypeArguments.mkString(",")}]"
      }
    }
  }

  val primitiveTypes: Set[Type] = Set(
    types.Bool,
    types.Byte,
    types.Int16,
    types.Char,
    types.Int32,
    types.Int64,
    types.Float32,
    types.Float64,
    types.IntBig,
    types.FloatBig,
    types.ByteArray,
    types.CharArray)

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
    classOf[java.lang.Character]  -> types.Char,
    java.lang.Character.TYPE      -> types.Char,
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
    classOf[Array[Byte]]
  ) ++ javaPrimitiveMappings.keys ++ javaPrimitiveMappings.values

  // TYPES

  def isPrimitiveValue(obj: Any) = supportedPrimitiveClasses.exists(clazz => clazz.isInstance(obj))
}
