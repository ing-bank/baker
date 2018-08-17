package com.ing.baker.types

trait TypeModule {

  def isApplicable(javaType: java.lang.reflect.Type): Boolean

  def readType(context: TypeContext, javaType: java.lang.reflect.Type): Type

  def toJava(context: TypeContext, value: Value, javaType: java.lang.reflect.Type): Any

  def fromJava(context: TypeContext, obj: Any): Value
}
