package com.ing.baker.runtime.recipe.ingredientExtractors

/**
  * Extracts ingredients from an object.
  */
trait IngredientExtractor {

  /**
    * Extracts the ingredient types from a given class.
    *
    * @param clazz The class
    *
    * @return The ingredient types.
    */
  def extractIngredientTypes(clazz: Class[_]): Map[String, Class[_]]

  /**
    * Extracts the ingredient data from a given object.
    *
    * @param obj The object.
    *
    * @return The ingredient data.
    */
  def extractIngredientData(obj: AnyRef): Map[String, Any]
}

