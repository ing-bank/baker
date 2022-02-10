package com.ing.baker.recipe.common

import java.util.Objects
import scala.collection.immutable.Seq

trait Event {
  val name: String
  val providedIngredients: Seq[Ingredient]
  val maxFiringLimit: Option[Int] = Option.empty

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Event =>
      this.name == other.name && this.providedIngredients == other.providedIngredients && this.maxFiringLimit == other.maxFiringLimit
    case _ =>
      false
  }

  override def hashCode(): Int = Objects.hash(name, providedIngredients, maxFiringLimit)

  override def toString: String = s"Event($name)"
}
