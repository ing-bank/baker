package com.ing.baker.compiler

import com.ing.baker.recipe.common.{Event, Ingredient, InteractionDescriptor, Recipe}

import scala.collection.immutable.Seq

object Assertions {
  private def assertNoDuplicateElementsExist[T](compareIdentifier: T => Any, elements: Set[T]): Unit = elements.foreach { e =>
    (elements - e).find(c => compareIdentifier(c) == compareIdentifier(e)).foreach { c => throw new IllegalStateException(s"Duplicate identifiers found: ${e.getClass.getSimpleName}:$e and ${c.getClass.getSimpleName}:$c") }
  }

  private def assertValidNames[T](nameFunc: T => String, list: Iterable[T], typeName: String): Unit = list.map(nameFunc).filter(name => name == null || name.isEmpty).foreach { _ =>
    throw new IllegalArgumentException(s"$typeName with a null or empty name found")
  }

  private def assertNonEmptyRecipe(recipe: Recipe): Seq[String] =
    Seq(
      Some("No sensory events found.").filter(_ => recipe.sensoryEvents.isEmpty),
      Some("No interactions found.").filter(_ => recipe.interactions.isEmpty)
    ).flatten

  private def assertSensoryEventsNegativeFiringLimits(recipe: Recipe): Seq[String] =
    Seq(
      Some("MaxFiringLimit should be greater than 0").filter(_ =>
        recipe.sensoryEvents.flatMap(_.maxFiringLimit).exists(_ <= 0)
      ),
    ).flatten

  def preCompileAssertions(recipe: Recipe): Seq[String] = {
    assertValidNames[Recipe](_.name, Seq(recipe), "Recipe")
    assertValidNames[InteractionDescriptor](_.name, recipe.interactions, "Interaction")
    assertValidNames[Event](_.name, recipe.sensoryEvents, "Event")
    val allIngredients = recipe.sensoryEvents.flatMap(_.providedIngredients) ++ recipe.interactions.flatMap(_.inputIngredients)
    assertValidNames[Ingredient](_.name, allIngredients, "Ingredient")
    assertNoDuplicateElementsExist[InteractionDescriptor](_.name, recipe.interactions.toSet)
    assertNoDuplicateElementsExist[Event](_.name, recipe.sensoryEvents)
    assertNonEmptyRecipe(recipe) ++ assertSensoryEventsNegativeFiringLimits(recipe)
  }
}
