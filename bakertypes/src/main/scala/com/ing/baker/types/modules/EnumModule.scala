package com.ing.baker.types.modules

import java.lang.reflect

import com.ing.baker.types._

class EnumModule extends TypeModule {

  override def isApplicable(javaType: reflect.Type): Boolean = javaType match {
    case clazz: Class[_] if clazz.isEnum => true
    case _ => false
  }

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = {

    javaType match {

      case enumClass: Class[_] if enumClass.isEnum =>
        EnumType(enumClass.asInstanceOf[Class[Enum[_]]].getEnumConstants.map(_.name).toSet)

      case unsupportedType =>
        throw new IllegalArgumentException(s"UnsupportedType: $unsupportedType")
    }
  }

  /**
    * Attempts to convert a java object to a value.
    *
    * @param obj The java object
    * @return a Value
    */
  override def fromJava(context: TypeAdapter, obj: Any): Value = {
    obj match {
      case enum if enum.getClass.isEnum => PrimitiveValue(enum.asInstanceOf[Enum[_]].name())
    }
  }

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    *
    * @return An instance of the java type.
    */
  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = {

    (value, javaType) match {
      case (NullValue, _) => null
      case (PrimitiveValue(option: String), clazz: Class[_]) if clazz.isEnum =>
        clazz.asInstanceOf[Class[Enum[_]]].getEnumConstants.find(_.name() == option) match {
          case Some(enumValue) => enumValue
          case None => throw new IllegalArgumentException(s"value '$option' is not an instance of enum: $clazz")
        }
    }
  }
}
