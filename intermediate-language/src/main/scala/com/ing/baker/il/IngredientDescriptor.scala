package com.ing.baker.il

import java.lang.reflect.Type

object IngredientDescriptor {
  val supportedBaseTypes: Set[Type] = Set(
    classOf[java.lang.Boolean],
    classOf[java.lang.Byte],
    classOf[java.lang.Short],
    classOf[java.lang.Character],
    classOf[java.lang.Integer],
    classOf[java.lang.Long],
    classOf[java.lang.Float],
    classOf[java.lang.Double],
    classOf[java.lang.String],
    classOf[java.math.BigDecimal],
    classOf[java.math.BigInteger]
  )
}

case class IngredientDescriptor(name: String, ingredientType: IngredientType) {

//  val clazz: Class[_] = getRawClass(ingredientType)
}
