package com.ing.baker.recipe.scaladsl


import com.ing.baker.recipe.common

import scala.reflect.runtime.{universe => ru}

object Ingredient {

  val mirror: ru.Mirror = ru.runtimeMirror(classOf[Ingredient[_]].getClassLoader)

  def asJavaType(paramType: ru.Type): java.lang.reflect.Type = {
    val typeConstructor = mirror.runtimeClass(paramType)
    val innerTypes = paramType.typeArgs.map(asJavaType).toArray

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

  def makeType[T : ru.TypeTag]: java.lang.reflect.Type = {
    asJavaType(ru.typeOf[T])
  }
}

case class Ingredient[T : ru.TypeTag](name: String) extends common.Ingredient {
  override val clazz: java.lang.reflect.Type = Ingredient.makeType[T]
}
