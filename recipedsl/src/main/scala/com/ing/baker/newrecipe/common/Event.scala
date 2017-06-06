package com.ing.baker.newrecipe.common

trait Event {
  val name: String
  val providedIngredients: Seq[Ingredient]

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Event => this.name == other.name && this.providedIngredients == other.providedIngredients
    case _ => false
  }

  override def toString(): String = toString("")
  def toString(appender: String): String = {
    s"""${appender}$name
       |${appender}providedIngredients: ${providedIngredients.foldLeft("(")((i, j) => s"$i, $j").replaceFirst(", ", "") + ")"}""".stripMargin
  }
}
