package com.ing.baker.recipe

package object scaladsl {

  val recipeInstanceId: Ingredient[String] = new Ingredient[String](common.recipeInstanceIdName)
  val recipeInstanceMetaData: Ingredient[Map[String, String]] = new Ingredient[Map[String, String]](common.recipeInstanceMetadataName)
  val recipeInstanceEventList: Ingredient[List[String]] = new Ingredient[List[String]](common.recipeInstanceEventListName)
}


