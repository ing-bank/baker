package com.ing.baker.types

import java.lang.reflect.ParameterizedType

import com.ing.baker.types.Converters.{createJavaType, mirror, readJavaType}
import com.ing.baker.types.modules.{CoreModule, JavaCollections, ScalaCollections}

import scala.reflect.runtime.universe

class TypeConverter {

  private val modules: Map[Class[_], TypeModule] = Map(

    classOf[java.util.List[_]] -> new JavaCollections.ListModule(),
    classOf[java.util.Set[_]] -> new JavaCollections.SetModule(),
    classOf[java.util.Map[_,_]] -> new JavaCollections.MapModule(),
    classOf[List[_]] -> new ScalaCollections.ListModule(),
    classOf[Set[_]] -> new ScalaCollections.SetModule(),
    classOf[Map[_,_]] -> new ScalaCollections.MapModule(),
    classOf[java.lang.Object] -> new CoreModule(),
  )


  /**
    * @param javaType
    * @return
    */
  def getModule(javaType: java.lang.reflect.Type): TypeModule = {

    val clazz: Class[_] = javaType match {
      case c: Class[_] => c
      case genericType: ParameterizedType => Converters.getBaseClass(genericType)
      case _ => throw new IllegalArgumentException(s"Incompatible type: $javaType")
    }

    modules.get(clazz) match {
      case Some(module) =>
        module
      case None =>

        val applicable = modules
          .filter { case (c, module) => (clazz.isPrimitive || c.isAssignableFrom(clazz)) &&  module.isApplicable(javaType) }
          .toList
          .sortWith { case ((clazzA, _), (clazzB, _)) => clazzB.isAssignableFrom(clazzA) }
          .map { case (_, module) => module }

        applicable.headOption.getOrElse(throw new IllegalStateException(s"No applicable module found for: $javaType"))
    }
  }

  def readType(javaType: java.lang.reflect.Type): Type = getModule(javaType).readType(this, javaType)

  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = getModule(javaType).toJava(this, value, javaType)

  def toJava[T : universe.TypeTag](value: Value): T = toJava(value, createJavaType(universe.typeOf[T])).asInstanceOf[T]

  def readType[T : universe.TypeTag]: Type = readJavaType(Converters.createJavaType(mirror.typeOf[T]))

  def fromJava(obj: Any): Value = {

    obj match {
      case null     => NullValue
      case v: Value => v
      case value if isPrimitiveValue(value) => PrimitiveValue(value)
      case _        =>
        val module = getModule(obj.getClass)
        module.fromJava(this, obj)
    }
  }
}

