package com.ing.baker.types

import java.lang.reflect.ParameterizedType

import scala.reflect.runtime.universe
import scala.reflect.runtime.universe.TypeTag

object Converters {

  val mirror: universe.Mirror = universe.runtimeMirror(classOf[Value].getClassLoader)

  val context = new TypeConverter()

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

  def readJavaType[T : TypeTag]: Type = readJavaType(createJavaType(mirror.typeOf[T]))

  def readJavaType(javaType: java.lang.reflect.Type): Type = context.readType(javaType)


  /**
    * Attempts to convert a java object to a value.
    *
    * @param obj The java object
    * @return a Value
    */
  def toValue(obj: Any): Value = context.fromJava(obj)

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    *
    * @return An instance of the java type.
    */
  @throws[IllegalArgumentException]("If failing to convert to the desired java type")
  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = context.toJava(value, javaType)

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @return An instance of the java type.
    */
  def toJava[T : universe.TypeTag](value: Value): T = toJava(value, createJavaType(universe.typeOf[T])).asInstanceOf[T]
}
