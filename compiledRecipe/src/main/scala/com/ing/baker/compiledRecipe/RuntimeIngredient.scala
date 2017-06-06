package com.ing.baker.compiledRecipe

case class RuntimeIngredient(name: String,
                             clazz: Class[_]) {
  override def equals(obj: scala.Any): Boolean = obj match {
    case other: RuntimeIngredient =>
      this.name == other.name &&
      this.clazz == other.clazz
    case _ => false
  }
}
