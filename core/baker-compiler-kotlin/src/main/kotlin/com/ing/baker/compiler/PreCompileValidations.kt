package com.ing.baker.compiler

import com.ing.baker.recipe.Event
import com.ing.baker.recipe.Ingredient
import com.ing.baker.recipe.Interaction
import com.ing.baker.recipe.Recipe

object PreCompileValidations {

    fun preCompileAssertions(recipe: Recipe): List<String> {
        assertValidNames(Recipe::name, listOf(recipe), "Recipe")
        assertValidNames(Interaction::name, recipe.interactions, "Interaction")
        assertValidNames(Event::name, recipe.sensoryEvents, "Event")
        assertValidNames(Ingredient::name, recipe.interactions.flatMap { it.inputIngredients }, "Ingredient")
        assertValidNames(Ingredient::name, recipe.sensoryEvents.flatMap { it.providedIngredients }, "Ingredient")

        assertNoDuplicateElementsExist(Interaction::name, recipe.interactions)
        assertNoDuplicateElementsExist(Event::name, recipe.sensoryEvents)

        return assertSensoryEventsNegativeFiringLimits(recipe) + assertRequiredEventForReprovider(recipe)
    }

    private fun <T> assertValidNames(nameFunc: (T) -> String?, list: Iterable<T>, typeName: String) =
        list.map(nameFunc)
            .firstOrNull { it.isNullOrEmpty() }
            ?.let { throw RecipeValidationException("$typeName with a null or empty name found") }

    private fun <T> assertNoDuplicateElementsExist(compareIdentifier: (T) -> Any, elements: Collection<T>) =
        elements
            .groupBy(compareIdentifier)
            .entries
            .firstOrNull { it.value.size > 1 }
            ?.let { (_, duplicates) ->
                val first = duplicates[0]
                val second = duplicates[1]
                throw RecipeValidationException(
                    "Duplicate identifiers found: ${first!!::class.simpleName}:$first and ${second!!::class.simpleName}:$second"
                )
            }

    private fun assertSensoryEventsNegativeFiringLimits(recipe: Recipe): List<String> =
        recipe.sensoryEvents
            .firstOrNull { it.maxFiringLimit != null && it.maxFiringLimit!! <= 0 }
            ?.let { listOf("MaxFiringLimit should be greater than 0") } ?: emptyList()

    private fun assertRequiredEventForReprovider(recipe: Recipe): List<String> =
        recipe.interactions
            .filter { interaction ->
                interaction.isReprovider && interaction.requiredEvents.isEmpty() && interaction.requiredOneOfEvents.isEmpty()
            }.map { interaction ->
                "Reprovider interaction ${interaction.name} needs to have a event precondition"
            }
}
