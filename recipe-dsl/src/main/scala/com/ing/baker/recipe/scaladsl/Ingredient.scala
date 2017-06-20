package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

import scala.reflect.ClassTag

case class Ingredient[I: ClassTag](override val name: String) extends common.Ingredient{
  override val clazz: Class[_] = implicitly[ClassTag[I]].runtimeClass
}