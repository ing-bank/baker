package com.ing.baker.types

import java.lang.reflect.{Modifier, ParameterizedType, Type}
import java.util
import java.util.Optional

import org.objenesis.ObjenesisStd

import scala.collection.JavaConverters._
import scala.reflect.runtime.universe
import scala.reflect.runtime.universe.TypeTag

object Converters {

  val mirror: universe.Mirror = universe.runtimeMirror(classOf[Value].getClassLoader)

  def getRawClass(t: Type): Class[_] = t match {
    case c: Class[_] => c
    case t: ParameterizedType => getRawClass(t.getRawType)
    case t@_ => throw new IllegalArgumentException(s"Unsupported type: $t")
  }

  def createJavaType(paramType: universe.Type): java.lang.reflect.Type = {
    val typeConstructor = mirror.runtimeClass(paramType)
    val innerTypes = paramType.typeArgs.map(createJavaType).toArray

    if (innerTypes.isEmpty) {
      typeConstructor
    } else {
      new java.lang.reflect.ParameterizedType {
        override def getRawType: java.lang.reflect.Type = typeConstructor
        override def getActualTypeArguments: Array[java.lang.reflect.Type] = innerTypes
        override def getOwnerType: java.lang.reflect.Type = null
        override def toString() = s"ParameterizedType: $typeConstructor[${getActualTypeArguments.mkString(",")}]"
      }
    }
  }

  def readJavaType[T : TypeTag]: BType = readJavaType(createJavaType(mirror.typeOf[T]))

  def readJavaType(javaType: Type): BType = {

    javaType match {
      case clazz if clazz == classOf[Object] =>
        throw new IllegalArgumentException(s"Unsupported type: $clazz")
      case clazz: Class[_] if supportedPrimitiveClasses.contains(clazz) =>
        PrimitiveType(clazz)
      case clazz: ParameterizedType if classOf[scala.Option[_]].isAssignableFrom(getRawClass(clazz)) || classOf[java.util.Optional[_]].isAssignableFrom(getRawClass(clazz)) =>
        val entryType = readJavaType(clazz.getActualTypeArguments()(0))
        OptionType(entryType)
      case clazz: ParameterizedType if getRawClass(clazz.getRawType).isAssignableFrom(classOf[List[_]]) || getRawClass(clazz.getRawType).isAssignableFrom(classOf[java.util.List[_]]) =>
        val entryType = readJavaType(clazz.getActualTypeArguments()(0))
        ListType(entryType)
      case clazz: ParameterizedType if getRawClass(clazz.getRawType).isAssignableFrom(classOf[Map[_,_]]) || getRawClass(clazz.getRawType).isAssignableFrom(classOf[java.util.Map[_,_]]) =>
        val keyType = clazz.getActualTypeArguments()(0)

        if (keyType != classOf[String])
          throw new IllegalArgumentException(s"Unsupported key type for map: $keyType")

        val valueType = readJavaType(clazz.getActualTypeArguments()(1))
        MapType(valueType)

      case enumClass: Class[_] if enumClass.isEnum =>
        EnumType(enumClass.asInstanceOf[Class[Enum[_]]].getEnumConstants.map(_.name).toSet)
      case pojoClass: Class[_] =>
        val fields = pojoClass.getDeclaredFields.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))
        val ingredients = fields.map(f => RecordField(f.getName, readJavaType(f.getGenericType)))
        RecordType(ingredients)
      case unsupportedType =>
        throw new IllegalArgumentException(s"UnsupportedType: $unsupportedType")
    }
  }

  def isEmpty(obj: Any) = {
    obj match {
      case null => true
      case None => true
      case option: java.util.Optional[_] if !option.isPresent => true
      case _ => false
    }
  }

  /**
    * Attempts to convert a java object to a value.
    *
    * @param obj
    * @return
    */
  def toValue(obj: Any): Value = {

    obj match {
      case value if isEmpty(value)          => NullValue
      case value if isPrimitiveValue(value) => PrimitiveValue(value)
      case list: List[_]                    => ListValue(list.map(toValue))
      case list: java.util.List[_]          => ListValue(list.asScala.toList.map(toValue))
      case map: java.util.Map[_, _]         =>
        val entries: Map[String, Value] = map.entrySet().iterator().asScala.map {
          e => e.getKey.asInstanceOf[String] -> e.getValue.toValue
        }.toMap
        RecordValue(entries)
      case map: Map[_, _] =>
        val entries: Map[String, Value] = map.map {
          case (name, value) => name.asInstanceOf[String] -> toValue(value)
        }
        RecordValue(entries)

      case Some(optionValue)                => toValue(optionValue)
      case option: java.util.Optional[_] if option.isPresent => toValue(option.get)
      case enum if enum.getClass.isEnum     => PrimitiveValue(enum.asInstanceOf[Enum[_]].name())
      case pojo                             =>
        val fields = pojo.getClass.getDeclaredFields.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))
        fields.foreach(_.setAccessible(true))

        val entries: Map[String, Value] = fields
          .map(f => f.getName -> toValue(f.get(pojo))).toMap

        RecordValue(entries)
    }
  }

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    * @return An instance of the java type.
    */
  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = {

    (value, javaType) match {
      case (_, clazz) if clazz == classOf[Object] =>
        throw new IllegalArgumentException(s"Unsupported type: $clazz")

      case (primitive: PrimitiveValue, clazz: Class[_]) if primitive.isAssignableTo(clazz) =>
        primitive.value

      case (PrimitiveValue(option: String), clazz: Class[_]) if clazz.isEnum =>
        clazz.asInstanceOf[Class[Enum[_]]].getEnumConstants.find(_.name() == option) match {
          case Some(enumValue) => enumValue
          case None => throw new IllegalArgumentException(s"option '$option' is not an instance of enum $clazz")
        }

      case (_, generic: ParameterizedType) if classOf[Option[_]].isAssignableFrom(getRawClass(generic.getRawType)) =>
        val optionType = generic.getActualTypeArguments()(0)
        value match {
          case NullValue =>
            None
          case _ =>
            val optionValue = toJava(value, optionType)
            Some(optionValue)
        }

      case (_, generic: ParameterizedType) if classOf[java.util.Optional[_]].isAssignableFrom(getRawClass(generic.getRawType)) =>
        val optionType = generic.getActualTypeArguments()(0)

        value match {
          case NullValue =>
            Optional.empty()
          case _ =>
            val optionValue = toJava(value, optionType)
            java.util.Optional.of(optionValue)
        }

      case (NullValue, _) =>
        null

      case (ListValue(entries), generic: ParameterizedType) if classOf[List[_]].isAssignableFrom(getRawClass(generic.getRawType)) =>
        val listType = generic.getActualTypeArguments()(0)
        entries.map(e => toJava(e, listType))

      case (ListValue(entries), generic: ParameterizedType) if classOf[java.util.List[_]].isAssignableFrom(getRawClass(generic.getRawType)) =>
        val listType = generic.getActualTypeArguments()(0)
        val list = new util.ArrayList[Any]()
        entries.foreach { e =>
          val value = toJava(e, listType)
          list.add(value)
        }
        list

      case (RecordValue(entries), generic: ParameterizedType) if classOf[java.util.Map[_,_]].isAssignableFrom(getRawClass(generic.getRawType)) =>
        val keyType = generic.getActualTypeArguments()(0)

        if (keyType != classOf[String])
          throw new IllegalArgumentException(s"Unsuported key type for map: $keyType")

        val valueType = generic.getActualTypeArguments()(1)

        val javaMap: java.util.Map[String, Any] = new util.HashMap[String, Any]()

        entries.foreach { case (name, value) => javaMap.put(name, toJava(value, valueType)) }

        javaMap

      case (RecordValue(entries), generic: ParameterizedType) if classOf[Map[_,_]].isAssignableFrom(getRawClass(generic.getRawType)) =>
        val keyType = generic.getActualTypeArguments()(0)

        if (keyType != classOf[String])
          throw new IllegalArgumentException(s"Unsuported key type for map: $keyType")

        val valueType = generic.getActualTypeArguments()(1)

        entries.map { case (name, value) => name -> toJava(value, valueType) }

      case (RecordValue(entries), pojoClass: Class[_]) =>

        // ObjenesisStd is somehow bypassing the constructor
        val objenesis = new ObjenesisStd // or ObjenesisSerializer

        val classInstantiator = objenesis.getInstantiatorOf(pojoClass)

        val pojoInstance = classInstantiator.newInstance()

        val fields = pojoClass.getDeclaredFields.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))

        fields.foreach { f =>
          entries.get(f.getName).foreach { entryValue =>
            val value = toJava(entryValue, f.getGenericType)
            f.setAccessible(true)
            f.set(pojoInstance, value)
          }
        }

        pojoInstance
    }
  }

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @return An instance of the java type.
    */
  def toJava[T : universe.TypeTag](value: Value): T = toJava(value, createJavaType(universe.typeOf[T])).asInstanceOf[T]
}
