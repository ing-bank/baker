package com.ing.baker.types.modules

import java.lang.reflect
import java.lang.reflect.ParameterizedType

import com.ing.baker.types.Converters._
import com.ing.baker.types._

object ScalaModules {

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

  class OptionModule extends TypeModule {
    override def isApplicable(javaType: reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, classOf[Option[_]])

    override def readType(context: TypeConverter, javaType: reflect.Type): Type = javaType match {
      case clazz: ParameterizedType if classOf[scala.Option[_]].isAssignableFrom(getBaseClass(clazz)) =>
        val entryType = context.readType(clazz.getActualTypeArguments()(0))
        OptionType(entryType)
    }

    override def toJava(context: TypeConverter, value: Value, javaType: reflect.Type): Any = (value, javaType) match {
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

    override def fromJava(context: TypeConverter, obj: Any): Value = obj match {
      case None      => NullValue
      case Some(obj) => context.fromJava(obj)
      case _ => throw new IllegalArgumentException(s"Unsupported object: $obj")
    }
  }
}



