package com.ing.baker.runtime.actor


trait RecipeMetadata {

  val recipeName: String

  def getAll: Set[ProcessMetadata]

  def add(meta: ProcessMetadata): Unit

  def remove(meta: ProcessMetadata): Unit
}
