package com.ing.baker.compiledRecipe.ingredientExtractors

import com.ing.baker.compiledRecipe.duplicates.ReflectionHelpers._

class PojoIngredientExtractor extends IngredientExtractor {
  override def extractIngredientData(obj: AnyRef): Map[String, Any] = {
    val clazz = obj.getClass
    clazz.getDeclaredFields.toSeq.map { field =>
      field.getName -> field.accessAndGet(obj)
    }.toMap
  }

  override def extractIngredientTypes(clazz: Class[_]): Map[String, Class[_]] =
    clazz.getDeclaredFields
      .filterNot(field => field.isSynthetic)
      .map(field => field.getName -> field.getType).toMap
}
