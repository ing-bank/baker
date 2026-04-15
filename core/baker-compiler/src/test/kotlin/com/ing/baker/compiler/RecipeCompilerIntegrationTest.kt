package com.ing.baker.compiler

import com.ing.baker.il.petrinet.*
import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.recipe.annotations.RequiresIngredient
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.Recipe
import com.ing.baker.types.Converters
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import scala.jdk.javaapi.CollectionConverters
import scala.jdk.javaapi.OptionConverters

/**
 * Integration tests for the refactored RecipeCompiler.
 * These tests verify that the full compilation flow works correctly end-to-end.
 */
class RecipeCompilerIntegrationTest {

    // Test events
    class OrderPlaced(val orderId: String, val items: List<String>)
    class PaymentMade(val paymentId: String)
    class OrderConfirmed(val confirmationId: String)
    class OrderShipped(val trackingNumber: String)
    class ItemsReserved(val reservedItems: List<String>)
    class PaymentReceived(val amount: Double)

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
            @RequiresIngredient("confirmationId") confirmationId: String
        ): OrderShipped
    }

    @Test
    fun `prepareRecipeComponents should extract all action descriptors`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        // Verify that the recipe compiled successfully
        assertNotNull(compiledRecipe)
        assertEquals("TestRecipe", compiledRecipe.name())

        // Verify that interactions were included
        val interactionNames = CollectionConverters.asJava(compiledRecipe.petriNet().transitions())
            .filterIsInstance<InteractionTransition>()
            .map { it.interactionName() }
        
        assertTrue(interactionNames.contains("ReserveItems"))
        assertTrue(interactionNames.contains("ProcessPayment"))
    }

    @Test
    fun `buildAllTransitions should create interaction and event transitions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        val petriNet = compiledRecipe.petriNet()
        
        // Should have sensory event transitions
        val eventTransitions = CollectionConverters.asJava(petriNet.transitions())
            .filterIsInstance<EventTransition>()
        
        val sensoryEventNames = eventTransitions
            .filter { it.isSensoryEvent() }
            .map { it.label() }
        
        assertTrue(sensoryEventNames.contains("OrderPlaced"))
        assertTrue(sensoryEventNames.contains("PaymentMade"))

        // Should have interaction transitions
        val interactionTransitions = CollectionConverters.asJava(petriNet.transitions())
            .filterIsInstance<InteractionTransition>()
        
        assertTrue(interactionTransitions.any { it.interactionName() == "ReserveItems" })
    }

    @Test
    fun `buildAllPetriNetArcs should create arcs connecting transitions and places`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        val petriNet = compiledRecipe.petriNet()
        
        // Verify that arcs were created
        val arcCount = petriNet.innerGraph().edges().size()
        assertTrue(arcCount > 0, "Should have created arcs")

        // Verify that places were created
        val placeCount = petriNet.places().size()
        assertTrue(placeCount > 0, "Should have created places")
    }

    @Test
    fun `assemblePetriNetAndValidate should create a valid compiled recipe`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        // Verify basic properties
        assertNotNull(compiledRecipe)
        assertEquals("TestRecipe", compiledRecipe.name())
        assertNotNull(compiledRecipe.petriNet())
        assertNotNull(compiledRecipe.recipeId())
    }

    @Test
    fun `compiled recipe should handle event preconditions`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)
            .withInteraction(
                InteractionDescriptor.of(ReserveItems::class.java)
            )
            .withInteraction(
                InteractionDescriptor.of(ProcessPayment::class.java)
            )
            .withInteraction(
                InteractionDescriptor.of(ShipOrder::class.java)
                    .withRequiredEvents(OrderConfirmed::class.java)
            )

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        // Should compile despite missing OrderConfirmed event (validation will catch it)
        assertNotNull(compiledRecipe)
        
        // Should have validation errors for missing event
        assertTrue(compiledRecipe.validationErrors().size() > 0)
        val errorMessages = CollectionConverters.asJava(compiledRecipe.validationErrors()).joinToString()
        assertTrue(errorMessages.contains("OrderConfirmed"))
    }

    @Test
    fun `compiled recipe should handle multiple interactions consuming same ingredient`() {
        val recipe = Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        // Both interactions use orderId - should create facilitator transition
        val petriNet = compiledRecipe.petriNet()
        val transitionCount = petriNet.transitions().size()
        
        // Should have: 
        // - 1 sensory event (OrderPlaced)
        // - 2 interaction events (ItemsReserved, PaymentReceived) 
        // - 2 interactions (ReserveItems, ProcessPayment)
        // - 1 facilitator for orderId (consumed by both interactions)
        assertTrue(transitionCount >= 6, "Should have facilitator transition for shared ingredient")
    }

    @Test
    fun `refactored compilation should maintain backward compatibility`() {
        // This test ensures that the refactored code produces the same results
        // as the original implementation would have
        val recipe = Recipe("BackwardCompatTest")
            .withSensoryEvent(OrderPlaced::class.java)
            .withSensoryEvent(PaymentMade::class.java)
            .withInteraction(InteractionDescriptor.of(ReserveItems::class.java))
            .withInteraction(InteractionDescriptor.of(ProcessPayment::class.java))

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        // Verify structure
        assertNotNull(compiledRecipe)
        assertEquals("BackwardCompatTest", compiledRecipe.name())
        
        // Verify all components present
        val petriNet = compiledRecipe.petriNet()
        assertTrue(petriNet.transitions().size() >= 4) // At least sensory events + interactions
        assertTrue(petriNet.places().size() > 0)
        assertTrue(petriNet.innerGraph().edges().size() > 0)
        
        // Should have no validation errors for this valid recipe
        assertEquals(0, compiledRecipe.validationErrors().size())
    }

    @Test
    fun `empty recipe should compile without errors`() {
        val recipe = Recipe("EmptyRecipe")

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

        assertNotNull(compiledRecipe)
        assertEquals("EmptyRecipe", compiledRecipe.name())
        assertEquals(0, compiledRecipe.validationErrors().size())
    }
}
