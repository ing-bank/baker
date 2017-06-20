package com.ing.baker.runtime.ingredient_extractors

import java.lang.reflect.Field

class PojoIngredientExtractor extends IngredientExtractor {
  implicit class FieldWithAdditions(field: Field) {
    def accessAndGet(obj: AnyRef) = {
      field.setAccessible(true)
      field.get(obj)
    }
  }

  override def extractIngredientData(obj: Any): Map[String, Any] = {
    val clazz = obj.getClass
    clazz.getDeclaredFields.toSeq.map { field =>
      field.getName -> field.accessAndGet(obj.asInstanceOf[AnyRef])
    }.toMap
  }

  override def extractIngredientTypes(clazz: Class[_]): Map[String, Class[_]] =
    clazz.getDeclaredFields
      .filterNot(field => field.isSynthetic)
      .map(field => field.getName -> field.getType).toMap
}
