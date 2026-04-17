package com.ing.baker.compiler

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.recipe.annotations.RequiresIngredient
import com.ing.baker.recipe.javadsl.CheckPointEvent
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.Recipe
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

class RecipeCompilerBasicTest {

    class EventA

    class EventB

    class EventC

    class EventD

    class EventE

    interface InteractionA : Interaction {

        interface ReserveItemsOutcome

        class OrderHadUnavailableItems(val unavailableItems: List<String>) : ReserveItemsOutcome

        class ItemsReserved(val reservedItems: List<String>) : ReserveItemsOutcome

        @FiresEvent(oneOf = [ItemsReserved::class, OrderHadUnavailableItems::class])
        fun apply(
            @RequiresIngredient("orderId") id: String,
            @RequiresIngredient("items") items: List<String>
        ): ReserveItemsOutcome
    }

    interface InteractionB : Interaction {

        interface ReserveItemsOutcome

        class OrderHadUnavailableItems(val unavailableItems: List<String>) : ReserveItemsOutcome

        class ItemsReserved(val reservedItems: List<String>) : ReserveItemsOutcome

        @FiresEvent(oneOf = [ItemsReserved::class, OrderHadUnavailableItems::class])
        fun apply(
            @RequiresIngredient("orderId") id: String,
            @RequiresIngredient("items") items: List<String>
        ): ReserveItemsOutcome
    }

    interface ReserveItemsOutcome

    @Test
    fun shouldCompileSimpleRecipe() {
        val recipe = Recipe("recipe")
            .withSensoryEvents(EventA::class.java)
        val compiled = RecipeCompiler.compileRecipe(recipe)

        Assertions.assertEquals("ed72cc8637c9cd07", compiled.recipeId())
    }

    @Test
    fun shouldCompileSimpleRecipeWithInteraction() {
        val recipe = Recipe("recipe")
            .withSensoryEvents(EventA::class.java)
            .withInteraction(InteractionDescriptor.of(InteractionA::class.java))
        val compiled = RecipeCompiler.compileRecipe(recipe)

        Assertions.assertEquals("9b2bc4caf5752697", compiled.recipeId())
    }

    @Test
    fun shouldAddInteractionsForCheckpointEvents() {
        val recipe = Recipe("recipe1")
            .withSensoryEvents(EventB::class.java, EventC::class.java, EventD::class.java)
            .withSensoryEventsNoFiringLimit(EventA::class.java)
            .withCheckpointEvent(
                CheckPointEvent("Success")
                    .withRequiredEvents(EventB::class.java, EventC::class.java)
            )

        val compiled = RecipeCompiler.compileRecipe(recipe)

        val actual = convertList(compiled.petriNet().transitions())
            .filterIsInstance<InteractionTransition>()
            .map { it.interactionName() }
            .toList()

        Assertions.assertEquals(listOf("\$CheckpointEventInteraction\$Success"), actual)
    }

    class SubSubSubEvent

    class SubSubEvent

    class SubEvent

    class Event

    @Test
    fun shouldAddSubRecipe() {
        // Several layers deep to verify if everything propagates correctly
        val subSubSubRecipe = Recipe("subSubSubRecipe")
            .withSensoryEvent(SubSubSubEvent::class.java)
            .withCheckpointEvent(CheckPointEvent("subSubSubCheckpointEvent"))
            .withInteraction(InteractionDescriptor.of(InteractionA::class.java))

        val subSubRecipe = Recipe("SubSubRecipe")
            .withSensoryEvent(SubSubEvent::class.java)
            .withSubRecipe(subSubSubRecipe)
            .withCheckpointEvent(CheckPointEvent("subSubCheckpointEvent"))
            .withInteraction(InteractionDescriptor.of(InteractionB::class.java))

        val subRecipe = Recipe("SubRecipe")
            .withSensoryEvent(SubEvent::class.java)
            .withSubRecipe(subSubRecipe)
            .withCheckpointEvent(CheckPointEvent("subCheckpointEvent"))
            .withInteraction(InteractionDescriptor.of(InteractionA::class.java))

        val recipe = Recipe("recipe")
            .withSensoryEvent(Event::class.java)
            .withSubRecipe(subRecipe)
            .withCheckpointEvent(CheckPointEvent("checkpointEvent"))

        val compiled = RecipeCompiler.compileRecipe(recipe)

        val actualSensoryEvents = convertList(compiled.sensoryEvents())
            .map { (it as com.ing.baker.il.EventDescriptor).name() }
            .toList()

        val expectedSensoryEvents = listOf("SubSubEvent", "SubEvent", "SubSubSubEvent", "Event")

        Assertions.assertEquals(expectedSensoryEvents, actualSensoryEvents)

        val actual = convertList(compiled.petriNet().transitions())
            .filterIsInstance<InteractionTransition>()
            .map { it.interactionName() }
            .toSet()

        val expected = setOf(
            $$"$CheckpointEventInteraction$subSubSubCheckpointEvent",
            $$"$SubRecipe$SubRecipe$InteractionA",
            $$"$CheckpointEventInteraction$subSubCheckpointEvent",
            $$"$CheckpointEventInteraction$subCheckpointEvent",
            $$"$CheckpointEventInteraction$checkpointEvent",
            $$"$SubRecipe$subSubSubRecipe$InteractionA",
            $$"$SubRecipe$SubSubRecipe$InteractionB"
        )

        Assertions.assertEquals(expected, actual)
    }

    private fun convertList(list: scala.collection.immutable.Set<*>): List<Any> {
        val result = mutableListOf<Any>()
        list.foreach { item ->
            result.add(item)
            item
        }
        return result
    }
}

