package com.ing.baker.recipe.common

trait Event {
  val name: String
  val providedIngredients: Seq[Ingredient]
  val maxFiringLimit: Option[Integer] = Option.empty

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Event => this.name == other.name && this.providedIngredients == other.providedIngredients
    case _ => false
  }

  override def toString(): String =  {
    s"""name: $name
       |providedIngredients: ${providedIngredients.mkString("(", ", ", ")")}""".stripMargin
  }
}
