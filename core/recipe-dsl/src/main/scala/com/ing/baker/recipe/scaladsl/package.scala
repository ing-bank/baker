package com.ing.baker.recipe

package object scaladsl {

  val recipeInstanceId: Ingredient[String] = new Ingredient[String](common.recipeInstanceIdName)
  val bakerMetadata: Ingredient[Map[String, String]] = new Ingredient[Map[String, String]](common.bakerMetaDataName)
  val bakerEventList: Ingredient[List[String]] = new Ingredient[List[String]](common.bakerEventList)
}


