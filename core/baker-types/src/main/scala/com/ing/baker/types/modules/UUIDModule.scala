package com.ing.baker.types.modules

import com.ing.baker.types._

import java.lang.reflect

import scala.annotation.nowarn

class UUIDModule extends TypeModule {

  override def isApplicable(javaType: reflect.Type): Boolean = javaType match {
    case clazz: Class[_] if clazz.isAssignableFrom(classOf[java.util.UUID]) => true
    case _ => false
  }

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    *
    * @return An instance of the java type.
    */
  @nowarn
  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = {
    (value, javaType) match {
      case (NullValue, _) => null
      case (PrimitiveValue(option: String), clazz: Class[_]) if clazz.isAssignableFrom(classOf[java.util.UUID]) =>
        java.util.UUID.fromString(option)
    }
  }

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = CharArray


  override def fromJava(context: TypeAdapter, obj: Any): Value = PrimitiveValue(obj.toString)

}
