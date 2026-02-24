package com.ing.baker.compiler

import com.ing.baker.recipe.common.Event
import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.common.InteractionDescriptor
import com.ing.baker.recipe.common.Recipe
import scala.Some

private fun <T: Any> assertNoDuplicateElementsExist(compareIdentifier: (T) -> Any, elements: Iterable<T>): Unit =
    when (val duplicates = elements.groupBy { compareIdentifier(it) }.values.firstOrNull { it.size > 1 }) {
        null -> Unit
        else -> {
            val e = duplicates[0]
            val c = duplicates[1]
            throw IllegalStateException("Duplicate identifiers found: ${e::class.java.getSimpleName()}:$e and ${c::class.java.getSimpleName()}:$c")
        }
    }

private fun <T: Any> assertValidNames(nameFunc: (T) -> String?, list: Iterable<T>, typeName: String): Unit =
    if (list.map(nameFunc).any { name -> (name == null) || (name.isEmpty())})
        throw IllegalArgumentException("$typeName with a null or empty name found")
    else
        Unit

private fun assertNonEmptyRecipe(recipe: Recipe): List<String> =
    listOf(
        if (recipe.sensoryEvents.isEmpty()) "No sensory events found." else null,
        if (recipe.interactions.isEmpty()) "No interactions found." else null,
    ).filterNotNull()

private fun assertRequiredEventForReprovider(recipe: Recipe): List<String> =
    recipe.interactions.filter { interaction ->
        interaction.isReprovider && interaction.requiredEvents.isEmpty() && interaction.requiredOneOfEvents.isEmpty()
    }.map{interaction -> "Reprovider interaction ${interaction.name()} needs to have a event precondition"}


private fun assertSensoryEventsNegativeFiringLimits(recipe: Recipe): List<String> =
    listOf(
        if (recipe.sensoryEvents.map(Event::maxFiringLimit).filterIsInstance(Some::class.java).any { it.value() as Int <= 0 }) "MaxFiringLimit should be greater than 0" else null
    ).filterNotNull()

fun preCompileAssertions(recipe: Recipe): List<String> {
    assertValidNames(Recipe::name, listOf(recipe), "Recipe")
    assertValidNames(InteractionDescriptor::name, recipe.interactions, "Interaction")
    assertValidNames(Event::name, recipe.sensoryEvents, "Event")
    val allIngredients = recipe.sensoryEvents.flatMap(Event::providedIngredients) + recipe.interactions.flatMap(InteractionDescriptor::inputIngredients)
    assertValidNames(Ingredient::name, allIngredients, "Ingredient")
    assertNoDuplicateElementsExist(InteractionDescriptor::name, recipe.interactions)
    assertNoDuplicateElementsExist<Event>(Event::name, recipe.sensoryEvents)
    return assertSensoryEventsNegativeFiringLimits(recipe) + assertRequiredEventForReprovider(recipe)
}