package com.ing.baker.types.modules

import java.lang.reflect.ParameterizedType
import java.util

import com.ing.baker.types._

import scala.collection.JavaConverters._

object JavaModules {

  class ListModule extends ClassModule[java.util.List[_]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): ListType = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): util.List[Any] = value match {
      case NullValue => null
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = getTypeParameter(javaType, 0)
        val list = new util.ArrayList[Any]()
        entries.foreach { e =>
          val value = context.toJava(e, entryType)
          list.add(value)
        }
        list
    }

    def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case list: java.util.List[_] => ListValue(list.asScala.toList.map(context.fromJava))
    }
  }

  class SetModule extends ClassModule[java.util.Set[_]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): ListType = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      ListType(entryType)
    }

    override  def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): util.Set[Any] = value match {
      case NullValue => null
      case ListValue(entries) if isApplicable(javaType) =>
        val entryType = getTypeParameter(javaType, 0)
        val list = new util.HashSet[Any]()
        entries.foreach { e =>
          val value = context.toJava(e, entryType)
          list.add(value)
        }
        list
    }

    def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case set: java.util.Set[_] => ListValue(set.asScala.toList.map(context.fromJava))
    }
  }

  class MapModule extends ClassModule[java.util.Map[_, _]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): MapType = {
      val entryType = context.readType(getTypeParameter(javaType, 0))
      MapType(entryType)
    }

    override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): util.Map[String, Any] = value match {
      case NullValue => null
      case RecordValue(entries) if classOf[java.util.Map[_,_]].isAssignableFrom(getBaseClass(javaType)) =>
        val keyType = getTypeParameter(javaType, 0)

        if (keyType != classOf[String])
          throw new IllegalArgumentException(s"Unsupported key type: $keyType")

        val valueType = getTypeParameter(javaType, 1)

        val javaMap = new util.HashMap[String, Any]()

        entries.foreach { case (name, _value) => javaMap.put(name, context.toJava(_value, valueType)) }

        javaMap
    }

    def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case map: java.util.Map[_, _] =>
        val entries: Map[String, Value] = map.entrySet().iterator().asScala.map {
          e => e.getKey.asInstanceOf[String] -> context.fromJava(e.getValue)
        }.toMap
        RecordValue(entries)
    }
  }

  class OptionalModule extends ClassModule[java.util.Optional[_]] {

    override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = javaType match {
      case clazz: ParameterizedType if isAssignableToBaseClass(javaType, classOf[java.util.Optional[_]]) =>
        val entryType = context.readType(clazz.getActualTypeArguments()(0))
        OptionType(entryType)
    }

    override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = (value, javaType) match {
      case (_, generic: ParameterizedType) if isAssignableToBaseClass(javaType, classOf[java.util.Optional[_]]) =>
        val optionType = generic.getActualTypeArguments()(0)
        value match {
          case NullValue =>
            java.util.Optional.empty()
          case _ =>
            val optionValue = context.toJava(value, optionType)
            java.util.Optional.of(optionValue)
        }
    }

    override def fromJava(context: TypeAdapter, obj: Any): Value = obj match {
      case optional: java.util.Optional[_] =>
        if (optional.isPresent)
          context.fromJava(optional.get())
        else
          NullValue
      case _ => throw new IllegalArgumentException(s"Unsupported object: $obj")
    }
  }
}


