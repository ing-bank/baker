package com.ing.baker.types

import com.ing.baker.types.modules.JavaCollections.ListModule

class TypeContext {

  private val modules: List[TypeModule] = List(
    new ListModule()
  )

  /**
    * considerations:
    *
    * - lookup of the module should be fast
    *
    * @param javaType
    * @return
    */
  def getModule(javaType: java.lang.reflect.Type) =
    modules.find(_.isApplicable(javaType))
      .getOrElse(throw new IllegalStateException(s"No applicable module found for: $javaType"))

  def readType(javaType: java.lang.reflect.Type): Type = {
    getModule(javaType).readType(this, javaType)
  }

  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = {
    getModule(javaType).toJava(this, value, javaType)
  }

  def fromJava(obj: Any): Value = ???
}

