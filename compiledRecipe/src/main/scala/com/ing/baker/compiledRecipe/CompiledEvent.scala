package com.ing.baker.compiledRecipe

case class CompiledEvent(name: String,
                         providedIngredients: Seq[CompiledIngredient]){
  override def equals(obj: scala.Any): Boolean = obj match {
    case other: CompiledEvent => this.name == other.name && this.providedIngredients == other.providedIngredients
    case _ => false
  }
}

object CompiledEvent{
  def apply(obj: Any): CompiledEvent = {
    CompiledEvent(obj.getClass.getSimpleName, obj.getClass.getDeclaredFields.map(CompiledIngredient(_)))
  }
}