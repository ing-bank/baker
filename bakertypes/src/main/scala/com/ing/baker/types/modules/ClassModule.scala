package com.ing.baker.types.modules

import java.lang.reflect

import com.ing.baker.types._

import scala.reflect.runtime.universe.TypeTag

abstract class ClassModule[T : TypeTag] extends TypeModule {

  protected val clazz = mirror.runtimeClass(mirror.typeOf[T])

  override def isApplicable(javaType: reflect.Type): Boolean = isAssignableToBaseClass(javaType, clazz)
}
