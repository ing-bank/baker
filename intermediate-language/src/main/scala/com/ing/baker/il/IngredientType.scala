package com.ing.baker.il

import java.lang.reflect.{ParameterizedType, Type}

case class IngredientType(name: String, javaType: Type) {

  val clazz: Class[_] = getRawClass(javaType)
}
