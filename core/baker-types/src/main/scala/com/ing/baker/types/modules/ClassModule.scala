package com.ing.baker.types.modules

import java.lang.reflect.Type

import com.ing.baker.types._

import scala.reflect.runtime.universe.TypeTag

abstract class ClassModule[T : TypeTag] extends TypeModule {

  protected val clazz: Class[_] = mirror.runtimeClass(mirror.typeOf[T])

  override def isApplicable(javaType: Type): Boolean = isAssignableToBaseClass(javaType, clazz)
}
