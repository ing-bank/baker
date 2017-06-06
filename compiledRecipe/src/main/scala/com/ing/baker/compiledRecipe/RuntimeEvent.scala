package com.ing.baker.compiledRecipe

case class RuntimeEvent(name: String,
                        providedIngredients: Seq[RuntimeIngredient]){
  override def equals(obj: scala.Any): Boolean = obj match {
    case other: RuntimeEvent => this.name == other.name && this.providedIngredients == other.providedIngredients
    case _ => false
  }
}
