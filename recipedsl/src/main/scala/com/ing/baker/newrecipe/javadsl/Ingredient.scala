package com.ing.baker.newrecipe.javadsl

import com.ing.baker.newrecipe.common

case class Ingredient(override val name: String, override val clazz: Class[_])
  extends common.Ingredient{
}


