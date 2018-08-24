package com.ing.baker.types.modules

import java.lang.reflect.ParameterizedType

import com.ing.baker.types
import com.ing.baker.types.Converters.getBaseClass
import com.ing.baker.types.{PrimitiveValue, Type, TypeConverter, TypeModule, Value, primitiveMappings}

class PrimitiveModule extends TypeModule {

  override def isApplicable(javaType: java.lang.reflect.Type): Boolean = {
    javaType match {
      case clazz: Class[_] => primitiveMappings.contains(clazz)
      case _ => false
    }
  }

  override def readType(context: TypeConverter, javaType: java.lang.reflect.Type): Type = {
    javaType match {
      case clazz: Class[_] => primitiveMappings(clazz)
      case t: ParameterizedType if classOf[scala.Array[_]].isAssignableFrom(getBaseClass(t)) && classOf[Byte].isAssignableFrom(getBaseClass(t.getActualTypeArguments()(0))) =>
        types.ByteArray
      case _ => throw new IllegalArgumentException(s"Unsupported type: $javaType")
    }
  }

  override def fromJava(context: TypeConverter, obj: Any): Value = PrimitiveValue(obj)

  override def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type): Any = {

    (value, javaType) match {
      case (p@PrimitiveValue(obj), clazz: Class[_]) if p.isAssignableTo(clazz) => obj
      case _ => throw new IllegalArgumentException(s"Unsupported type: $javaType")
    }
  }
}
