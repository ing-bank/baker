package com.ing.baker.compiledRecipe

case class RuntimeEvent(name: String,
                        providedIngredients: Seq[RuntimeIngredient]){
  override def equals(obj: scala.Any): Boolean = obj match {
    case other: RuntimeEvent => this.name == other.name && this.providedIngredients == other.providedIngredients
    case _ => false
  }
}

object RuntimeEvent{
  def apply(obj: Any): RuntimeEvent = {
    RuntimeEvent(obj.getClass.getSimpleName, obj.getClass.getDeclaredFields.map(RuntimeIngredient(_)))
  }

  def apply(eventImpl: EventImpl): RuntimeEvent = {
    RuntimeEvent(eventImpl.name, eventImpl.getClass.getDeclaredFields.map(RuntimeIngredient(_)))
  }
}