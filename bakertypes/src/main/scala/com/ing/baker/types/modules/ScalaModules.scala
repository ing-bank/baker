package com.ing.baker.types.modules

import java.lang.reflect
import java.lang.reflect.ParameterizedType

import com.ing.baker.types._

object ScalaModules {

  class ListModule extends ClassModule[List[_]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type) = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case NullValue => null
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = getTypeParameter(javaType, 0)
        entries.map(v => context.toJava(v, entryType))
    }

    def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case list: List[_] => ListValue(list.map(context.fromJava))
    }
  }

  class SetModule extends ClassModule[Set[_]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type) = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case NullValue => null
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = getTypeParameter(javaType, 0)
        entries.map(v => context.toJava(v, entryType)).toSet
    }

    def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case set: Set[_] => ListValue(set.toList.map(context.fromJava))
    }
  }

  class MapModule extends ClassModule[Map[_, _]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type) = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type) = value match {
      case NullValue => null
      case RecordValue(entries) if classOf[Map[_,_]].isAssignableFrom(getBaseClass(javaType)) =>
        val keyType = getTypeParameter(javaType, 0)

        if (keyType != classOf[String])
          throw new IllegalArgumentException(s"Unsuported key type: $keyType")

        val valueType = getTypeParameter(javaType, 1)

        entries.mapValues { value => context.toJava(value, valueType) }
    }

    def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case map: Map[_, _] =>
        val entries: Map[String, Value] = map.map { case (key, obj) => key.asInstanceOf[String] -> context.fromJava(obj) }.toMap
        RecordValue(entries)
    }
  }

  class OptionModule extends ClassModule[Option[_]] {

    override def readType(context: TypeAdapter, javaType: reflect.Type): Type = javaType match {
      case clazz: ParameterizedType if classOf[scala.Option[_]].isAssignableFrom(getBaseClass(clazz)) =>
        val entryType = context.readType(clazz.getActualTypeArguments()(0))
        OptionType(entryType)
    }

    override def toJava(context: TypeAdapter, value: Value, javaType: reflect.Type): Any = (value, javaType) match {
      case (_, generic: ParameterizedType) if classOf[Option[_]].isAssignableFrom(getBaseClass(generic.getRawType)) =>
        val optionType = generic.getActualTypeArguments()(0)
        value match {
          case NullValue =>
            None
          case _ =>
            val optionValue = context.toJava(value, optionType)
            Some(optionValue)
        }
    }

    override def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case None      => NullValue
      case Some(obj) => context.fromJava(obj)
      case _ => throw new IllegalArgumentException(s"Unsupported object: $obj")
    }
  }
}



