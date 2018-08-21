package com.ing.baker.types

trait TypeModule {

  def isApplicable(javaType: java.lang.reflect.Type): Boolean

  def readType(context: TypeConverter, javaType: java.lang.reflect.Type): Type

  def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type): Any

  def fromJava(context: TypeConverter, obj: Any): Value
}
