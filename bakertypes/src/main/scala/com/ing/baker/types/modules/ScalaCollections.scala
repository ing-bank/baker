package com.ing.baker.types.modules

import java.lang.reflect.ParameterizedType
import java.util

import com.ing.baker.types._

import scala.collection.JavaConverters._
import Converters._

object ScalaCollections {

  def getTypeParameter(javaType: java.lang.reflect.Type, index: Int): java.lang.reflect.Type = {
    javaType.asInstanceOf[ParameterizedType].getActualTypeArguments()(index)
  }

  class ListModule extends TypeModule {

    val baseClass = classOf[List[_]]

    override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, baseClass)

    override def readType(context: TypeConverter, javaType: java.lang.reflect.Type) = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = getTypeParameter(javaType, 0)
        entries.map(v => context.toJava(v, entryType))
    }

    def fromJava(context: TypeConverter, obj: Any): Value = obj match {
      case list: List[_] => ListValue(list.toList.map(context.fromJava))
    }
  }

  class SetModule extends TypeModule {

    val baseClass = classOf[Set[_]]

    override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, baseClass)

    override def readType(context: TypeConverter, javaType: java.lang.reflect.Type) = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = getTypeParameter(javaType, 0)
        entries.map(v => context.toJava(v, entryType)).toSet
    }

    def fromJava(context: TypeConverter, obj: Any): Value = obj match {
      case set: Set[_] => ListValue(set.toList.map(context.fromJava))
    }
  }

  class MapModule extends TypeModule {

    val baseClass = classOf[Map[_, _]]

    override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, baseClass)

    override def readType(context: TypeConverter, javaType: java.lang.reflect.Type) = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case RecordValue(entries) if classOf[Map[_,_]].isAssignableFrom(getBaseClass(javaType)) =>
        val keyType = getTypeParameter(javaType, 0)

        if (keyType != classOf[String])
          throw new IllegalArgumentException(s"Unsuported key type: $keyType")

        val valueType = getTypeParameter(javaType, 1)

        entries.mapValues { value => context.toJava(value, valueType) }
    }

    def fromJava(context: TypeConverter, obj: Any): Value = obj match {
      case map: Map[_, _] =>
        val entries: Map[String, Value] = map.map { case (key, obj) => key.asInstanceOf[String] -> context.fromJava(obj) }.toMap
        RecordValue(entries)
    }
  }
}



