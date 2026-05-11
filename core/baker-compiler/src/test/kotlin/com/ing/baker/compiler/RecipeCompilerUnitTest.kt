package com.ing.baker.compiler

import com.ing.baker.compiler.RecipeCompiler.interactionTransitionOf
import com.ing.baker.il.ValidationSettings
import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.recipe.annotations.RequiresIngredient
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.Recipe
import com.ing.baker.recipe.toKotlin
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())

        assertEquals(2, actionDescriptors.size, "Should extract 2 interactions")
        assertEquals(1, sensoryEvents.count(), "Should extract 1 sensory event")
        assertTrue(actionDescriptors.any { it.name == "ReserveItems" })
        assertTrue(actionDescriptors.any { it.name == "ProcessPayment" })
    }

    @Test
    fun `prepareRecipeComponents extracts all ingredient names`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val (_, _, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())

        assertTrue(allIngredientNames.contains("orderId"), "Should include orderId from OrderPlaced")
        assertTrue(allIngredientNames.contains("items"), "Should include items from OrderPlaced")
        assertTrue(allIngredientNames.contains("reservedItems"), "Should include reservedItems from ItemsReserved output")
    }

    @Test
    fun `prepareRecipeComponents handles empty recipe`() {
        val recipe = Recipe("EmptyRecipe")

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())

        assertEquals(0, actionDescriptors.size)
        assertEquals(0, sensoryEvents.count())
        assertEquals(0, allIngredientNames.size)
    }

    @Test
    fun `buildAllTransitions creates interaction transitions for each interaction`() {
        val recipe = Recipe("TestRecipe")
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
        val transitions = RecipeCompiler.buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy()
        )
        val arcs = RecipeCompiler.buildAllPetriNetArcs(actionDescriptors, transitions)
        
        val compiledRecipe = RecipeCompiler.assemblePetriNetAndValidate(
            recipe.toKotlin(),
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

        val (actionDescriptors, sensoryEvents, allIngredientNames) = RecipeCompiler.prepareRecipeComponents(recipe.toKotlin())
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
            recipe.toKotlin(),
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
        // Create test data using builders
        val interactionTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ReserveItems",
            inputIngredientNames = listOf("orderId", "items"),
            outputEventNames = listOf("ItemsReserved"),
            outputEventIngredients = mapOf("ItemsReserved" to listOf("reservedItems"))
        )
        val eventTransition = TestDataBuilders.eventTransition(
            eventName = "ItemsReserved",
            isSensory = false,
            ingredientNames = listOf("reservedItems")
        )
        
        val arcs = RecipeCompiler.buildInternalEventArcs(
            listOf(interactionTransition),
            listOf(eventTransition)
        )

        // ItemsReserved event has reservedItems ingredient - should create arcs
        assertTrue(arcs.isNotEmpty(), "Should create arcs for event ingredients")
    }

    @Test
    fun `buildEventLimiterArcs creates arcs for sensory event transitions`() {
        // Create sensory event transitions with firing limits using builders
        val event1 = TestDataBuilders.eventTransition(
            eventName = "OrderPlaced",
            isSensory = true,
            maxFiringLimit = 1,
            ingredientNames = listOf("orderId", "items")
        )
        val event2 = TestDataBuilders.eventTransition(
            eventName = "PaymentMade",
            isSensory = true,
            maxFiringLimit = 1,
            ingredientNames = listOf("paymentId")
        )
        
        val arcs = RecipeCompiler.buildEventLimiterArcs(listOf(event1, event2))

        // Sensory events with firing limits should have limiter arcs
        assertTrue(arcs.isNotEmpty(), "Should create event limiter arcs for sensory events with firing limits")
    }

    @Test
    fun `buildEventPreconditionArcs creates arcs for required events (AND)`() {
        // Create event transitions using builders
        val itemsReservedEvent = TestDataBuilders.eventTransition("ItemsReserved", isSensory = false)
        val paymentMadeEvent = TestDataBuilders.eventTransition("PaymentMade", isSensory = true)
        
        // Create interaction transition with required events
        val shipOrderInteraction = TestDataBuilders.simpleInteractionTransition(
            name = "ShipOrder",
            inputIngredientNames = listOf("orderId", "reservedItems")
        )
        
        // Create interaction descriptor with preconditions
        val shipOrderDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions(
            name = "ShipOrder",
            requiredEvents = setOf("ItemsReserved", "PaymentMade")
        )
        
        val arcs = RecipeCompiler.buildEventPreconditionArcs(
            listOf(itemsReservedEvent, paymentMadeEvent),
            listOf(shipOrderInteraction),
            listOf(shipOrderDescriptor)
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
        // Create event transitions using builders
        val itemsReservedEvent = TestDataBuilders.eventTransition("ItemsReserved", isSensory = false)
        val paymentReceivedEvent = TestDataBuilders.eventTransition("PaymentReceived", isSensory = false)
        
        // Create interaction transition
        val shipOrderInteraction = TestDataBuilders.simpleInteractionTransition(
            name = "ShipOrder",
            inputIngredientNames = listOf("orderId", "reservedItems")
        )
        
        // Create interaction descriptor with OR preconditions
        val shipOrderDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions(
            name = "ShipOrder",
            requiredOneOfEvents = setOf(setOf("ItemsReserved", "PaymentReceived"))
        )
        
        val arcs = RecipeCompiler.buildEventPreconditionArcs(
            listOf(itemsReservedEvent, paymentReceivedEvent),
            listOf(shipOrderInteraction),
            listOf(shipOrderDescriptor)
        )

        // ShipOrder requires ItemsReserved OR PaymentReceived
        // Should create precondition arcs connecting both events to the same OR place
        assertTrue(arcs.isNotEmpty(), "Should create arcs for OR event preconditions")
        
        // With 2 OR events, we expect: 2 arcs from events to shared place + 1 arc from place to interaction
        assertTrue(arcs.size >= 3, "Should create arcs for OR preconditions")
    }

    @Test
    fun `buildEventPreconditionArcs handles interactions without preconditions`() {
        // Create interaction transitions without preconditions using builders
        val reserveItemsInteraction = TestDataBuilders.simpleInteractionTransition(
            name = "ReserveItems",
            inputIngredientNames = listOf("orderId", "items")
        )
        val processPaymentInteraction = TestDataBuilders.simpleInteractionTransition(
            name = "ProcessPayment",
            inputIngredientNames = listOf("orderId", "paymentId")
        )
        
        // Create descriptors without preconditions
        val reserveDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions("ReserveItems")
        val processDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions("ProcessPayment")
        
        val arcs = RecipeCompiler.buildEventPreconditionArcs(
            emptyList(),
            listOf(reserveItemsInteraction, processPaymentInteraction),
            listOf(reserveDescriptor, processDescriptor)
        )

        // No interactions have required events, so no precondition arcs should be created
        assertEquals(0, arcs.size, "Should not create arcs when no event preconditions are defined")
    }

    @Test
    fun `buildPreconditionErrors reports missing required events (AND)`() {
        // Create transitions with only one event
        val itemsReservedEvent = TestDataBuilders.eventTransition("ItemsReserved", isSensory = false)
        val shipOrderTransition = TestDataBuilders.simpleInteractionTransition("ShipOrder")
        
        val transitions = TestDataBuilders.transitionCollections(
            interactionTransitions = listOf(shipOrderTransition),
            sensoryEventTransitions = emptyList(),
            interactionEventTransitions = listOf(itemsReservedEvent)
        )
        
        // Create descriptor that requires both ItemsReserved and PaymentReceived
        val shipOrderDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions(
            name = "ShipOrder",
            requiredEvents = setOf("ItemsReserved", "PaymentReceived")
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, listOf(shipOrderDescriptor))

        // ShipOrder requires PaymentReceived which doesn't exist
        assertTrue(errors.isNotEmpty(), "Should report missing required event")
        assertTrue(errors.any { it.contains("PaymentReceived") && it.contains("ShipOrder") }, 
            "Error should mention missing PaymentReceived event for ShipOrder")
    }

    @Test
    fun `buildPreconditionErrors reports missing required one-of events (OR)`() {
        // Create transitions with no events
        val shipOrderTransition = TestDataBuilders.simpleInteractionTransition("ShipOrder")
        
        val transitions = TestDataBuilders.transitionCollections(
            interactionTransitions = listOf(shipOrderTransition),
            sensoryEventTransitions = emptyList(),
            interactionEventTransitions = emptyList()
        )
        
        // Create descriptor that requires ItemsReserved OR PaymentReceived (neither exists)
        val shipOrderDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions(
            name = "ShipOrder",
            requiredOneOfEvents = setOf(setOf("ItemsReserved", "PaymentReceived"))
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, listOf(shipOrderDescriptor))

        // ShipOrder requires ItemsReserved OR PaymentReceived, neither exists
        assertTrue(errors.size >= 2, "Should report all missing OR events")
        assertTrue(errors.any { it.contains("ItemsReserved") }, "Should report missing ItemsReserved")
        assertTrue(errors.any { it.contains("PaymentReceived") }, "Should report missing PaymentReceived")
    }

    @Test
    fun `buildPreconditionErrors returns empty when all required events exist`() {
        // Create transitions with all required events
        val itemsReservedEvent = TestDataBuilders.eventTransition("ItemsReserved", isSensory = false)
        val paymentReceivedEvent = TestDataBuilders.eventTransition("PaymentReceived", isSensory = false)
        val shipOrderTransition = TestDataBuilders.simpleInteractionTransition("ShipOrder")
        
        val transitions = TestDataBuilders.transitionCollections(
            interactionTransitions = listOf(shipOrderTransition),
            sensoryEventTransitions = emptyList(),
            interactionEventTransitions = listOf(itemsReservedEvent, paymentReceivedEvent)
        )
        
        // Create descriptor that requires both events (both exist)
        val shipOrderDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions(
            name = "ShipOrder",
            requiredEvents = setOf("ItemsReserved", "PaymentReceived")
        )
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, listOf(shipOrderDescriptor))

        // All required events exist
        assertEquals(0, errors.size, "Should not report errors when all required events exist")
    }

    @Test
    fun `buildPreconditionErrors handles interactions without preconditions`() {
        // Create transitions without preconditions
        val reserveItemsTransition = TestDataBuilders.simpleInteractionTransition("ReserveItems")
        val processPaymentTransition = TestDataBuilders.simpleInteractionTransition("ProcessPayment")
        
        val transitions = TestDataBuilders.transitionCollections(
            interactionTransitions = listOf(reserveItemsTransition, processPaymentTransition),
            sensoryEventTransitions = emptyList(),
            interactionEventTransitions = emptyList()
        )
        
        // Create descriptors without preconditions
        val reserveDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions("ReserveItems")
        val processDescriptor = TestDataBuilders.interactionDescriptorWithPreconditions("ProcessPayment")
        
        val errors = RecipeCompiler.buildPreconditionErrors(transitions, listOf(reserveDescriptor, processDescriptor))

        // No interactions have required events
        assertEquals(0, errors.size, "Should not report errors when no preconditions are defined")
    }

    @Test
    fun `buildSensoryEventArcs creates arcs for events with ingredients`() {
        // Create sensory event transition with ingredients using builder
        val orderPlacedEvent = TestDataBuilders.eventTransition(
            eventName = "OrderPlaced",
            isSensory = true,
            ingredientNames = listOf("orderId", "items")
        )
        
        val arcs = RecipeCompiler.buildSensoryEventArcs(listOf(orderPlacedEvent), emptyList())

        // OrderPlaced has orderId and items ingredients
        assertTrue(arcs.size >= 2, "Should create arcs for each ingredient")
    }

    @Test
    fun `buildMultipleOutputFacilitatorArcs creates arc for each facilitator transition`() {
        // Create interaction transitions that share orderId ingredient
        val reserveItemsTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ReserveItems",
            inputIngredientNames = listOf("orderId", "items")
        )
        val processPaymentTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ProcessPayment",
            inputIngredientNames = listOf("orderId", "paymentId")
        )
        
        // Build facilitator transitions for shared ingredients
        val facilitatorTransitions = RecipeCompiler.buildMultipleOutputFacilitatorTransitions(
            listOf(reserveItemsTransition, processPaymentTransition)
        )
        
        val arcs = RecipeCompiler.buildMultipleOutputFacilitatorArcs(facilitatorTransitions)

        // Should have facilitator arcs for shared ingredients (orderId)
        assertTrue(arcs.isNotEmpty(), "Should create facilitator arcs")
        assertEquals(facilitatorTransitions.size, arcs.size, 
            "Should have one arc per facilitator transition")
    }

    @Test
    fun `buildInteractionArcs creates arcs for all interactions`() {
        // Create interaction transitions using builders
        val reserveItemsTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ReserveItems",
            inputIngredientNames = listOf("orderId", "items"),
            outputEventNames = listOf("ItemsReserved")
        )
        val processPaymentTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ProcessPayment",
            inputIngredientNames = listOf("orderId", "paymentId"),
            outputEventNames = listOf("PaymentReceived")
        )
        
        // Create event transitions for interaction outputs
        val itemsReservedEvent = TestDataBuilders.eventTransition("ItemsReserved", isSensory = false)
        val paymentReceivedEvent = TestDataBuilders.eventTransition("PaymentReceived", isSensory = false)
        
        // Build facilitator transitions
        val facilitatorTransitions = RecipeCompiler.buildMultipleOutputFacilitatorTransitions(
            listOf(reserveItemsTransition, processPaymentTransition)
        )
        
        val arcs = RecipeCompiler.buildInteractionArcs(
            listOf(reserveItemsTransition, processPaymentTransition),
            facilitatorTransitions,
            listOf(itemsReservedEvent, paymentReceivedEvent)
        )

        assertTrue(arcs.isNotEmpty(), "Should create interaction arcs")
        // Should have input arcs (ingredients -> interaction) and output arcs (interaction -> events)
    }

    // ========== Helper Function Tests ==========

    @Test
    fun `buildMultipleOutputFacilitatorTransitions creates transitions for shared ingredients`() {
        // Create interaction transitions that share orderId ingredient
        val reserveItemsTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ReserveItems",
            inputIngredientNames = listOf("orderId", "items")
        )
        val processPaymentTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ProcessPayment",
            inputIngredientNames = listOf("orderId", "paymentId")
        )
        
        val facilitatorTransitions = RecipeCompiler.buildMultipleOutputFacilitatorTransitions(
            listOf(reserveItemsTransition, processPaymentTransition)
        )

        // Both interactions require orderId
        assertTrue(facilitatorTransitions.isNotEmpty(), "Should create facilitator for orderId")
        assertTrue(facilitatorTransitions.any { it.label() == "orderId" })
    }

    @Test
    fun `buildMultipleOutputFacilitatorTransitions returns empty when no shared ingredients`() {
        // Create single interaction transition using builder
        val reserveItemsTransition = TestDataBuilders.simpleInteractionTransition(
            name = "ReserveItems",
            inputIngredientNames = listOf("orderId", "items")
        )
        
        val facilitatorTransitions = RecipeCompiler.buildMultipleOutputFacilitatorTransitions(
            listOf(reserveItemsTransition)
        )

        // Only one interaction, no shared ingredients
        assertEquals(0, facilitatorTransitions.size, "Should not create facilitators when no sharing")
    }
}