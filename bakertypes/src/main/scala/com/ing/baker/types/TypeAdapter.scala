package com.ing.baker.types

import java.lang.reflect.ParameterizedType

import com.ing.baker.types.Converters.readJavaType
import com.ing.baker.types.modules._

import scala.reflect.runtime.universe

class TypeAdapter(private val modules: Map[Class[_], TypeModule]) {

  private val primitiveModule = new PrimitiveModule()

  /**
    * @param javaType
    * @return
    */
  def getOptionalModule(javaType: java.lang.reflect.Type): Option[TypeModule] = {

    val clazz: Class[_] = javaType match {
      case c: Class[_] => c
      case genericType: ParameterizedType => getBaseClass(genericType)
      case _ => throw new IllegalArgumentException(s"Incompatible type: $javaType")
    }

    if (clazz.isPrimitive || primitiveModule.isApplicable(clazz))
      Some(primitiveModule)
    else
      modules.get(clazz) match {
        case Some(module) => Some(module)
        case None =>

          val applicable = modules
            .filter { case (c, module) => c.isAssignableFrom(clazz) && module.isApplicable(javaType) }
            .toList
            .sortWith { case ((clazzA, _), (clazzB, _)) => clazzB.isAssignableFrom(clazzA) }
            .map { case (_, module) => module }

          applicable.headOption
      }
  }

  def getModule(javaType: java.lang.reflect.Type): TypeModule = {
    getOptionalModule(javaType)
      .getOrElse(throw new IllegalStateException(s"No applicable module found for: $javaType"))
  }

  def readType(javaType: java.lang.reflect.Type): Type = getModule(javaType).readType(this, javaType)

  def toJava(value: Value, javaType: java.lang.reflect.Type): Any =

    getOptionalModule(javaType) match {
      case Some(module) => module.toJava(this, value, javaType)
      case None if value.isNull => null
      case _ => throw new IllegalStateException(s"No applicable module found for: $javaType")
    }

  def toJava[T : universe.TypeTag](value: Value): T = toJava(value, createJavaType(universe.typeOf[T])).asInstanceOf[T]

  def readType[T : universe.TypeTag]: Type = readJavaType(createJavaType(mirror.typeOf[T]))

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

