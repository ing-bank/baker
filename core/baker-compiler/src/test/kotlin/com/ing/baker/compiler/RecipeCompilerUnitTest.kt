package com.ing.baker.compiler

import com.ing.baker.compiler.RecipeCompiler.interactionTransitionOf
import com.ing.baker.il.ValidationSettings
import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.recipe.annotations.RequiresIngredient
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.Recipe
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import scala.jdk.javaapi.CollectionConverters

/**
 * Unit tests for individual refactored methods in RecipeCompiler.
 * Each test calls a specific extracted method directly with minimal test data.
 */
class RecipeCompilerUnitTest {

    // Test events
    class OrderPlaced(val orderId: String, val items: List<String>)
    class PaymentMade(val paymentId: String)
    class ItemsReserved(val reservedItems: List<String>)
    class PaymentReceived(val amount: Double)
    class OrderShipped(val trackingNumber: String)

    // Test interactions
    interface ReserveItems : Interaction {
        @FiresEvent(oneOf = [ItemsReserved::class])
        fun apply(
            @RequiresIngredient("orderId") orderId: String,
            @RequiresIngredient("items") items: List<String>
        ): ItemsReserved
    }

    interface ProcessPayment : Interaction {
        @FiresEvent(oneOf = [PaymentReceived::class])
        fun apply(
            @RequiresIngredient("orderId") orderId: String,
            @RequiresIngredient("paymentId") paymentId: String
        ): PaymentReceived
    }

    interface ShipOrder : Interaction {
        @FiresEvent(oneOf = [OrderShipped::class])
        fun apply(
            @RequiresIngredient("orderId") orderId: String,
            @RequiresIngredient("reservedItems") items: List<String>
        ): OrderShipped
    }

    // ========== Phase Function Tests ==========

    @Test
    fun `prepareRecipeComponents extracts interactions from recipe`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)

        assertEquals(2, actionDescriptors.size, "Should extract 2 interactions")
        assertEquals(1, sensoryEvents.count(), "Should extract 1 sensory event")
        assertTrue(actionDescriptors.any { it.name() == "ReserveItems" })
        assertTrue(actionDescriptors.any { it.name() == "ProcessPayment" })
    }

    @Test
    fun `prepareRecipeComponents extracts all ingredient names`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (_, _, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)

        assertTrue(allIngredientNames.contains("orderId"), "Should include orderId from OrderPlaced")
        assertTrue(allIngredientNames.contains("items"), "Should include items from OrderPlaced")
        assertTrue(allIngredientNames.contains("reservedItems"), "Should include reservedItems from ItemsReserved output")
    }

    @Test
    fun `prepareRecipeComponents handles empty recipe`() {
        val recipe = Recipe("EmptyRecipe")

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)

        assertEquals(0, actionDescriptors.size)
        assertEquals(0, sensoryEvents.count())
        assertEquals(0, allIngredientNames.size)
    }

    @Test
    fun `buildAllTransitions creates interaction transitions for each interaction`() {
        val recipe = Recipe("TestRecipe")
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )

        assertEquals(2, transitions.allInteractionTransitions.size, "Should create 2 interaction transitions")
        assertTrue(transitions.allInteractionTransitions.any { it.interactionName() == "ReserveItems" })
        assertTrue(transitions.allInteractionTransitions.any { it.interactionName() == "ProcessPayment" })
    }

    @Test
    fun `buildAllTransitions creates sensory event transitions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )

        assertEquals(2, transitions.sensoryEventTransitions.size, "Should create 2 sensory event transitions")
        assertTrue(transitions.sensoryEventTransitions.all { it.isSensoryEvent() })
        assertTrue(transitions.sensoryEventTransitions.any { it.label() == "OrderPlaced" })
        assertTrue(transitions.sensoryEventTransitions.any { it.label() == "PaymentMade" })
    }

    @Test
    fun `buildAllTransitions creates interaction event transitions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )

        assertEquals(1, transitions.interactionEventTransitions.size, "Should create transition for ItemsReserved event")
        assertFalse(transitions.interactionEventTransitions[0].isSensoryEvent(), "Interaction events are not sensory")
        assertEquals("ItemsReserved", transitions.interactionEventTransitions[0].label())
    }

    @Test
    fun `buildAllTransitions creates facilitator transitions for shared ingredients`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )

        // Both ReserveItems and ProcessPayment require orderId
        assertTrue(transitions.multipleOutputFacilitatorTransitions.size > 0, "Should create facilitator for orderId")
        assertTrue(
            transitions.multipleOutputFacilitatorTransitions.any { it.label() == "orderId" },
            "Should have facilitator transition for orderId"
        )
    }

    @Test
    fun `buildAllTransitions combines all event transitions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )

        val expectedCount = transitions.sensoryEventTransitions.size + transitions.interactionEventTransitions.size
        assertEquals(expectedCount, transitions.allEventTransitions.size, "allEventTransitions should combine both types")
    }

    @Test
    fun `buildAllPetriNetArcs creates arcs from multiple sources`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        val arcs = RecipeCompiler.buildAllPetriNetArcs(actionDescriptors, transitions)

        assertTrue(arcs.isNotEmpty(), "Should create arcs")
        // Arcs should include: interaction arcs, sensory event arcs, internal event arcs, etc.
    }

    @Test
    fun `assemblePetriNetAndValidate creates CompiledRecipe with Petri net`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        val arcs = RecipeCompiler.buildAllPetriNetArcs(actionDescriptors, transitions)
        
        val compiledRecipe = RecipeCompiler.assemblePetriNetAndValidate(
            recipe,
            arcs,
            emptyList(),
            emptyList(),
            ValidationSettings.defaultValidationSettings()
        )

        assertNotNull(compiledRecipe)
        assertEquals("TestRecipe", compiledRecipe.name())
        assertNotNull(compiledRecipe.petriNet())
        assertNotNull(compiledRecipe.recipeId())
    }

    @Test
    fun `assemblePetriNetAndValidate includes validation errors`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        val arcs = RecipeCompiler.buildAllPetriNetArcs(actionDescriptors, transitions)
        
        val precompileErrors = listOf("Test error 1")
        val preconditionErrors = listOf("Test error 2")
        val compiledRecipe = RecipeCompiler.assemblePetriNetAndValidate(
            recipe,
            arcs,
            precompileErrors,
            preconditionErrors,
            ValidationSettings.defaultValidationSettings()
        )

        val errors = CollectionConverters.asJava(compiledRecipe.validationErrors())
        assertTrue(errors.contains("Test error 1"))
        assertTrue(errors.contains("Test error 2"))
    }

    // ========== Arc Building Function Tests ==========

    @Test
    fun `buildInternalEventArcs creates arcs for event ingredients`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildInternalEventArcs(
            transitions.allInteractionTransitions,
            transitions.interactionEventTransitions
        )

        // ItemsReserved event has reservedItems ingredient
        assertTrue(arcs.isNotEmpty(), "Should create arcs for event ingredients")
    }

    @Test
    fun `buildEventLimiterArcs creates arcs for sensory event transitions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)

        val (_, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            emptyList(),
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildEventLimiterArcs(transitions.sensoryEventTransitions)

        // Sensory events have limiters by default
        assertTrue(arcs.isNotEmpty(), "Should create event limiter arcs for sensory events")
    }

    @Test
    fun `buildEventPreconditionArcs creates arcs for required events (AND)`() {
        // Create recipe with interaction that requires a specific event
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(
                InteractionDescriptor.of(ShipOrder::class.java)
                    .withRequiredEvents(ItemsReserved::class.java, PaymentMade::class.java)
            )

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildEventPreconditionArcs(
            transitions.allEventTransitions,
            transitions.allInteractionTransitions,
            actionDescriptors
        )

        // ShipOrder requires ItemsReserved AND PaymentMade
        // Should create precondition arcs for both required events
        assertTrue(arcs.isNotEmpty(), "Should create arcs for event preconditions")
        
        // With 2 required events, we expect arcs for both preconditions
        // Each precondition creates 2 arcs: event->place and place->interaction
        assertTrue(arcs.size >= 4, "Should create arcs for both AND preconditions (2 events * 2 arcs each)")
    }

    @Test
    fun `buildEventPreconditionArcs creates arcs for required one-of events (OR)`() {
        // Create recipe with interaction that requires one of several events
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))
            .withInteraction(
                InteractionDescriptor.of(ShipOrder::class.java)
                    .withRequiredOneOfEvents(ItemsReserved::class.java, PaymentReceived::class.java)
            )

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildEventPreconditionArcs(
            transitions.allEventTransitions,
            transitions.allInteractionTransitions,
            actionDescriptors
        )

        // ShipOrder requires ItemsReserved OR PaymentReceived
        // Should create precondition arcs connecting both events to the same OR place
        assertTrue(arcs.isNotEmpty(), "Should create arcs for OR event preconditions")
        
        // With 2 OR events, we expect: 2 arcs from events to shared place + 1 arc from place to interaction
        assertTrue(arcs.size >= 3, "Should create arcs for OR preconditions")
    }

    @Test
    fun `buildEventPreconditionArcs handles interactions without preconditions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildEventPreconditionArcs(
            transitions.allEventTransitions,
            transitions.allInteractionTransitions,
            actionDescriptors
        )

        // No interactions have required events, so no precondition arcs should be created
        assertEquals(0, arcs.size, "Should not create arcs when no event preconditions are defined")
    }

    @Test
    fun `buildPreconditionErrors reports missing required events (AND)`() {
        // Create recipe where ShipOrder requires an event that doesn't exist
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(
                InteractionDescriptor.of(ShipOrder::class.java)
                    .withRequiredEvents(ItemsReserved::class.java, PaymentReceived::class.java)
            )

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, actionDescriptors)

        // ShipOrder requires PaymentReceived which doesn't exist (ProcessPayment interaction is missing)
        assertTrue(errors.isNotEmpty(), "Should report missing required event")
        assertTrue(errors.any { it.contains("PaymentReceived") && it.contains("ShipOrder") }, 
            "Error should mention missing PaymentReceived event for ShipOrder")
    }

    @Test
    fun `buildPreconditionErrors reports missing required one-of events (OR)`() {
        // Create recipe where interaction requires one of several events, none of which exist
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(
                InteractionDescriptor.of(ShipOrder::class.java)
                    .withRequiredOneOfEvents(ItemsReserved::class.java, PaymentReceived::class.java)
            )

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, actionDescriptors)

        // ShipOrder requires ItemsReserved OR PaymentReceived, neither exists
        assertTrue(errors.size >= 2, "Should report all missing OR events")
        assertTrue(errors.any { it.contains("ItemsReserved") }, "Should report missing ItemsReserved")
        assertTrue(errors.any { it.contains("PaymentReceived") }, "Should report missing PaymentReceived")
    }

    @Test
    fun `buildPreconditionErrors returns empty when all required events exist`() {
        // Create recipe where all required events are provided
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))
            .withInteraction(
                InteractionDescriptor.of(ShipOrder::class.java)
                    .withRequiredEvents(ItemsReserved::class.java, PaymentReceived::class.java)
            )

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, actionDescriptors)

        // All required events exist (ItemsReserved from ReserveItems, PaymentReceived from ProcessPayment)
        assertEquals(0, errors.size, "Should not report errors when all required events exist")
    }

    @Test
    fun `buildPreconditionErrors handles interactions without preconditions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, actionDescriptors)

        // No interactions have required events
        assertEquals(0, errors.size, "Should not report errors when no preconditions are defined")
    }

    @Test
    fun `buildSensoryEventArcs creates arcs for events with ingredients`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildSensoryEventArcs(transitions.sensoryEventTransitions, actionDescriptors)

        // OrderPlaced has orderId and items ingredients
        assertTrue(arcs.size >= 2, "Should create arcs for each ingredient")
    }

    @Test
    fun `buildMultipleOutputFacilitatorArcs creates arc for each facilitator transition`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildMultipleOutputFacilitatorArcs(transitions.multipleOutputFacilitatorTransitions)

        // Should have facilitator arcs for shared ingredients (orderId)
        assertTrue(arcs.isNotEmpty(), "Should create facilitator arcs")
        assertEquals(transitions.multipleOutputFacilitatorTransitions.size, arcs.size, 
            "Should have one arc per facilitator transition")
    }

    @Test
    fun `buildInteractionArcs creates arcs for all interactions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        
        val arcs = RecipeCompiler.buildInteractionArcs(
            transitions.allInteractionTransitions,
            transitions.multipleOutputFacilitatorTransitions,
            transitions.interactionEventTransitions
        )

        assertTrue(arcs.isNotEmpty(), "Should create interaction arcs")
        // Should have input arcs (ingredients -> interaction) and output arcs (interaction -> events)
    }

    // ========== Helper Function Tests ==========

    @Test
    fun `buildMultipleOutputFacilitatorTransitions creates transitions for shared ingredients`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val interactionTransitions = actionDescriptors.map { 
            interactionTransitionOf(it, recipe.defaultFailureStrategy(), allIngredientNames) 
        }
        
        val facilitatorTransitions = RecipeCompiler.buildMultipleOutputFacilitatorTransitions(interactionTransitions)

        // Both interactions require orderId
        assertTrue(facilitatorTransitions.isNotEmpty(), "Should create facilitator for orderId")
        assertTrue(facilitatorTransitions.any { it.label() == "orderId" })
    }

    @Test
    fun `buildMultipleOutputFacilitatorTransitions returns empty when no shared ingredients`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe)
        val interactionTransitions = actionDescriptors.map { 
            interactionTransitionOf(it, recipe.defaultFailureStrategy(), allIngredientNames) 
        }
        
        val facilitatorTransitions = RecipeCompiler.buildMultipleOutputFacilitatorTransitions(interactionTransitions)

        // Only one interaction, no shared ingredients
        assertEquals(0, facilitatorTransitions.size, "Should not create facilitators when no sharing")
    }
}