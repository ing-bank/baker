package com.ing.baker.types.modules

import java.lang.reflect.ParameterizedType
import java.util

import com.ing.baker.types.Converters.{isAssignableToBaseClass, toValue}
import com.ing.baker.types.{ListType, ListValue, TypeConverter, TypeModule, Value}

import scala.collection.JavaConverters._

object JavaCollections {

  class ListModule extends TypeModule {

    val baseClass = classOf[java.util.List[_]]

    override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, classOf[java.util.List[_]])

    override def readType(context: TypeConverter, javaType: java.lang.reflect.Type) = {
      val genericType = javaType.asInstanceOf[ParameterizedType]
      val entryType = context.readType(genericType.getActualTypeArguments()(0))
      ListType(entryType)
    }

    override  def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = javaType.asInstanceOf[ParameterizedType].getActualTypeArguments()(0)
        val list = new util.ArrayList[Any]()
        entries.foreach { e =>
          val value = context.toJava(e, entryType)
          list.add(value)
        }
        list
    }

    def fromJava(context: TypeConverter, obj: Any): Value = obj match {
      case list: java.util.List[_] => ListValue(list.asScala.toList.map(toValue))
    }
  }
}


