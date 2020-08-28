package com.ing.baker.types

trait TypeModule {

  def isApplicable(javaType: java.lang.reflect.Type): Boolean

  def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type

  def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any

  def fromJava(context: TypeAdapter, obj: Any): Value
}
