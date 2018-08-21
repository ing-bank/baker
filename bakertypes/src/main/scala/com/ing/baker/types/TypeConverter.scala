package com.ing.baker.types

import com.ing.baker.types.Converters.{createJavaType, mirror, readJavaType}
import com.ing.baker.types.modules.CoreModule
import com.ing.baker.types.modules.JavaCollections.ListModule

import scala.reflect.runtime.universe

class TypeConverter {

  private val modules: Map[java.lang.reflect.Type, TypeModule] = Map(

    classOf[java.util.List[_]] -> new ListModule(),
    classOf[java.lang.Object] -> new CoreModule()
  )


  /**
    * considerations:
    *
    * - lookup of the module should be fast
    *
    * @param javaType
    * @return
    */
  def getModule(javaType: java.lang.reflect.Type): TypeModule = {

    modules.get(javaType) match {
      case Some(module) =>
        module
      case None =>
        modules.values.find(_.isApplicable(javaType))
          .getOrElse(throw new IllegalStateException(s"No applicable module found for: $javaType"))
    }
  }

  def readType(javaType: java.lang.reflect.Type): Type = {
    getModule(javaType).readType(this, javaType)
  }

  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = {
    getModule(javaType).toJava(this, value, javaType)
  }

  def toJava[T : universe.TypeTag](value: Value): T = toJava(value, createJavaType(universe.typeOf[T])).asInstanceOf[T]

  def readType[T : universe.TypeTag]: Type = readJavaType(Converters.createJavaType(mirror.typeOf[T]))

  def fromJava(obj: Any): Value = {

    obj match {
      case null => NullValue
      case _    => getModule(obj.getClass).fromJava(this, obj)
    }
  }
}

