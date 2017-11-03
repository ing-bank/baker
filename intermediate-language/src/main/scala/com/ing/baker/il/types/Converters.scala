package com.ing.baker.il.types

import java.lang.reflect.{Modifier, ParameterizedType, Type}
import java.util
import java.util.Optional

import com.ing.baker.il.CompiledRecipe
import org.objenesis.ObjenesisStd

import scala.collection.JavaConverters._
import scala.reflect.runtime.universe

object Converters {

  val mirror: universe.Mirror = universe.runtimeMirror(classOf[CompiledRecipe].getClassLoader)

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
      case value if isEmpty(value)          => throw new IllegalArgumentException(s"Non supported value: $obj")
      case value if isPrimitiveValue(value) => PrimitiveValue(value)
      case list: List[_]                    => ListValue(list.map(toValue))
      case list: java.util.List[_]          => ListValue(list.asScala.toList.map(toValue))
      case Some(optionValue)                => toValue(optionValue)
      case option: java.util.Optional[_] if option.isPresent => toValue(option.get)
      case pojo                             =>
        val fields = pojo.getClass.getDeclaredFields.filterNot(_.isSynthetic)
        fields.foreach(_.setAccessible(true))

        val entries: Map[String, Value] = fields
          .map(f => f.getName -> toValue(f.get(pojo))).toMap

        RecordValue(entries)
    }
  }

  /**
    * This check is not exhaustive, see also:
    *
    * https://stackoverflow.com/questions/7525142/how-to-programmatically-determine-if-the-the-class-is-a-case-class-or-a-simple-c
    */
  def isCaseClass(clazz: Class[_]) = clazz.getInterfaces.exists(_ == classOf[scala.Product])

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    * @return An instance of the java type.
    */
  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = {

    (value, javaType) match {
      case (primitive: PrimitiveValue, clazz: Class[_]) if primitive.isAssignableTo(clazz) =>
        primitive.value
      case (_, generic: ParameterizedType) if getRawClass(generic.getRawType) == classOf[Option[_]] =>
        val optionType = generic.getActualTypeArguments()(0)
        value match {
          case NullValue =>
            None
          case _ =>
            val optionValue = toJava(value, optionType)
            Some(optionValue)
        }

      case (_, generic: ParameterizedType) if getRawClass(generic.getRawType) == classOf[java.util.Optional[_]] =>
        val optionType = generic.getActualTypeArguments()(0)

        value match {
          case NullValue =>
            Optional.empty()
          case _ =>
            val optionValue = toJava(value, optionType)
            java.util.Optional.of(optionValue)
        }

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

      case (RecordValue(entries), pojoClass: Class[_]) =>

        // ObjenesisStd is somehow bypassing the constructor
        val objenesis = new ObjenesisStd // or ObjenesisSerializer

        val classInstantiator = objenesis.getInstantiatorOf(pojoClass)

        val pojoInstance = classInstantiator.newInstance()

        val fields = pojoClass.getDeclaredFields.filterNot(_.isSynthetic)

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
