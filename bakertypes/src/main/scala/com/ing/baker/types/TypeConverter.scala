package com.ing.baker.types

import java.lang.reflect.ParameterizedType

import com.ing.baker.types.Converters.{createJavaType, mirror, readJavaType}
import com.ing.baker.types.modules._

import scala.reflect.runtime.universe

class TypeConverter {

  private val primitiveModule = new PrimitiveModule()

  private val modules: Map[Class[_], TypeModule] = Map(

    classOf[java.util.List[_]] -> new JavaModules.ListModule(),
    classOf[java.util.Set[_]] -> new JavaModules.SetModule(),
    classOf[java.util.Map[_,_]] -> new JavaModules.MapModule(),
    classOf[java.util.Optional[_]] -> new JavaModules.OptionalModule(),
    classOf[List[_]] -> new ScalaModules.ListModule(),
    classOf[Set[_]] -> new ScalaModules.SetModule(),
    classOf[Map[_,_]] -> new ScalaModules.MapModule(),
    classOf[Option[_]] -> new ScalaModules.OptionModule(),
    classOf[java.lang.Enum[_]] -> new EnumModule(),
    classOf[AnyRef] -> new PojoModule()
  )

  /**
    * @param javaType
    * @return
    */
  def getOptionalModule(javaType: java.lang.reflect.Type): Option[TypeModule] = {

    val clazz: Class[_] = javaType match {
      case c: Class[_] => c
      case genericType: ParameterizedType => Converters.getBaseClass(genericType)
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
      case None if value.isNull => NullValue
      case _ => throw new IllegalStateException(s"No applicable module found for: $javaType")
    }

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

