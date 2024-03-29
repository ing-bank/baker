package com.ing.baker.types.modules

import java.lang.reflect.ParameterizedType

import com.ing.baker.types
import com.ing.baker.types._
import java.lang.reflect.{Type => JType}

class PrimitiveModule extends TypeModule {

  private def isByteArray(javaType: JType) = javaType match {
    case clazz: Class[_] =>
      clazz == classOf[Array[Byte]]
    case t: ParameterizedType =>
      classOf[scala.Array[_]].isAssignableFrom(getBaseClass(t)) && classOf[Byte].isAssignableFrom(getBaseClass(t.getActualTypeArguments()(0)))
  }

  override def isApplicable(javaType: JType): Boolean = {
    javaType match {
      case clazz: Class[_] => primitiveMappings.contains(clazz)
      case other           => isByteArray(other)
    }
  }

  override def readType(context: TypeAdapter, javaType: JType): Type = {
    javaType match {
      case clazz: Class[_] => primitiveMappings(clazz)
      case other if isByteArray(other) => types.ByteArray
      case _ => throw new IllegalArgumentException(s"Unsupported type: $javaType")
    }
  }

  override def fromJava(context: TypeAdapter, obj: Any): Value = PrimitiveValue(obj)

  override def toJava(context: TypeAdapter, value: Value, javaType: JType): Any = {

    (value, javaType) match {
      case (p @ PrimitiveValue(obj), clazz: Class[_]) if p.isAssignableTo(clazz) => obj
      case (p @ PrimitiveValue(obj), other) if isByteArray(other) && obj.getClass.isArray => obj
      case (NullValue, clazz: Class[_]) if !clazz.isPrimitive => null
      case _ => throw new IllegalArgumentException(s"$value cannot be instantiated as: $javaType")
    }
  }
}
