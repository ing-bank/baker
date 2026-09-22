package com.ing.baker.runtime.inmemory

import com.google.common.collect.ImmutableList
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.inmemory.recipe.CustomerInfo
import com.ing.baker.runtime.inmemory.recipe.LogRecipeFailedImpl
import com.ing.baker.runtime.inmemory.recipe.ManufactureGoods
import com.ing.baker.runtime.inmemory.recipe.SendInvoice
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.CustomerInfoReceived
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.OrderPlaced
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.PaymentMade
import com.ing.baker.runtime.inmemory.recipe.ShipGoods
import com.ing.baker.runtime.inmemory.recipe.ValidateOrder
import com.ing.baker.runtime.inmemory.recipe.WebShopRecipe
import com.ing.baker.runtime.javadsl.EventInstance
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.mockito.ArgumentMatchers.anyString
import org.mockito.Mock
import org.mockito.Mockito
import org.mockito.Mockito.times
import org.mockito.Mockito.verify
import org.mockito.Mockito.verifyNoInteractions
import org.mockito.Mockito.`when`
import org.mockito.MockitoAnnotations
import java.time.Duration
import java.util.UUID

/**
 * Example of a unit test for a recipe.
 *
 * It assumes you mock all interactions and implement tests for all important cases,
 * using just the recipe and sensory events.
 */
class WebShopRecipeTest {

    @Mock
    lateinit var manufactureGoods: ManufactureGoods

    @Mock
    lateinit var sendInvoice: SendInvoice

    @Mock
    lateinit var shipGoods: ShipGoods

    @Mock
    lateinit var validateOrder: ValidateOrder

    @OptIn(ExperimentalDsl::class)
    val recipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe)

    @BeforeEach
    fun setUp() {
        MockitoAnnotations.openMocks(this)
    }

    private fun setupMockImplementations(): List<Any> {
        return ImmutableList.of(manufactureGoods, sendInvoice, shipGoods, validateOrder, LogRecipeFailedImpl())
    }

    /**
     * A simple happy flow tests for the recipe.
     * This ensures the recipe when executed does what we expect.
     *
     * @throws Exception
     */
    @Test
    @Throws(Exception::class)
    fun testHappyFlowWebShopRecipe() {

        Assertions.assertEquals(ImmutableList.of<Any>(), recipe.validationErrors, "Validate that recipe has no validation errors")
        val baker = InMemoryBaker.java(setupMockImplementations())

        // Add recipe
        baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

        val goods = "goods"
        val order = "order"
        val trackingId = "trackingId"
        val customerInfo = CustomerInfo("name", "address", "email")

        // Prepare mock responses - use doReturn/when to avoid null pointer issues with Kotlin
        // For non-string parameters, we don't specify them exactly as Mockito's any() returns null for Kotlin non-nullable types
        Mockito.doReturn(ValidateOrder.OrderValid()).`when`(validateOrder).apply(anyString(), anyString())
        Mockito.doReturn(ManufactureGoods.GoodsManufactured(goods)).`when`(manufactureGoods).apply(anyString())
        Mockito.doReturn(SendInvoice.InvoiceSent()).`when`(sendInvoice).apply(customerInfo)
        Mockito.doReturn(ShipGoods.GoodsShipped(trackingId)).`when`(shipGoods).apply(goods, customerInfo)

        val recipeInstanceId = UUID.randomUUID().toString()
        // Create recipe instance, we use blocking code here since its a unit test.
        baker.bake(recipe.recipeId(), recipeInstanceId).get()

        // Fire events into Baker
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(OrderPlaced(order))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(CustomerInfoReceived(customerInfo))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(PaymentMade())).get()
        baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(5)).join()

        // Validate that mocks were called
        verify(validateOrder).apply(anyString(), anyString())
        verify(manufactureGoods).apply(anyString())

        // Ensure events appeared - awaitCompleted waits for the recipe instance to become fully idle,
        // so by this point the whole happy flow (including ShipGoods, SendInvoice and the
        // RecipeSuccessful checkpoint event) has completed.
        val expectedEvents = ImmutableList.of(
            "OrderPlaced",
            "OrderValid",
            "CustomerInfoReceived",
            "PaymentMade",
            "GoodsManufactured",
            "GoodsShipped",
            "InvoiceSent",
            "RecipeSuccessful"
        )
        val events = baker.getEventNames(recipeInstanceId).get()
        Assertions.assertEquals(
            HashSet(expectedEvents),
            HashSet(events),
            "Expected events not found. Got events: $events"
        )
    }

    /**
     * A simple unhappy flow tests for the recipe.
     * We use this to test that interactions are not executed if case of a validation failure.
     *
     * @throws Exception
     */
    @Test
    @Throws(Exception::class)
    fun testUnHappyFlowWebShopRecipe() {

        Assertions.assertEquals(ImmutableList.of<Any>(), recipe.validationErrors, "Validate that recipe has no validation errors")
        val baker = InMemoryBaker.java(setupMockImplementations())

        // Add recipe
        baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

        val order = "order"
        val customerInfo = CustomerInfo("name", "address", "email")

        // Prepare mock responses
        `when`(validateOrder.apply(anyString(), anyString()))
            .thenReturn(ValidateOrder.OrderInvalid())

        val recipeInstanceId = UUID.randomUUID().toString()
        // Create recipe instance, we use blocking code here since it's a unit test.
        baker.bake(recipe.recipeId(), recipeInstanceId).get()

        // Fire events into Baker
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(OrderPlaced(order))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(CustomerInfoReceived(customerInfo))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(PaymentMade())).get()
        baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(5)).join()

        // Validate that mocks where called with correct data
        verify(validateOrder).apply(recipeInstanceId, order)
        verifyNoInteractions(manufactureGoods)
        verifyNoInteractions(sendInvoice)
        verifyNoInteractions(shipGoods)

        // Ensure events appeared
        val expectedEvents = ImmutableList.of(
            "OrderPlaced",
            "OrderInvalid",
            "CustomerInfoReceived",
            "PaymentMade"
        )

        val events = baker.getEventNames(recipeInstanceId).get()
        Assertions.assertEquals(
            HashSet(expectedEvents),
            HashSet(events)
        )
    }

    /**
     * This tests validates the exception handling and retry strategy of this recipe.
     * The ShipGoods will fail but will retry and pass the second time.
     * The SendInvoice will fail but not retry following its retry strategy.
     * We manually retry the SendInvoice by calling the retryInteraction.
     *
     * @throws Exception
     */
    @Test
    @Throws(Exception::class)
    fun testTechnicalFailureWebShopRecipe() {
        Assertions.assertEquals(ImmutableList.of<Any>(), recipe.validationErrors, "Validate that recipe has no validation errors")
        val baker = InMemoryBaker.java(setupMockImplementations())

        // Add recipe
        baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

        val goods = "goods"
        val order = "order"
        val trackingId = "trackingId"
        val customerInfo = CustomerInfo("name", "address", "email")

        // Prepare mock responses
        `when`(validateOrder.apply(anyString(), anyString()))
            .thenReturn(ValidateOrder.OrderValid())

        `when`(manufactureGoods.apply(anyString()))
            .thenReturn(ManufactureGoods.GoodsManufactured(goods))

        // For methods with non-nullable object parameters, we don't use any() matcher to avoid null issues with Kotlin
        // Instead we rely on Mockito's default answer to handle any invocation
        `when`(sendInvoice.apply(customerInfo))
            .thenThrow(RuntimeException("Expected failure"))
            .thenReturn(SendInvoice.InvoiceSent())

        `when`(shipGoods.apply(goods, customerInfo))
            .thenThrow(RuntimeException("Expected failure"))
            .thenReturn(ShipGoods.GoodsShipped(trackingId))

        val recipeInstanceId = UUID.randomUUID().toString()
        // Create recipe instance, we use blocking code here since it's a unit test.
        baker.bake(recipe.recipeId(), recipeInstanceId).get()

        // Fire events into Baker
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(OrderPlaced(order))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(CustomerInfoReceived(customerInfo))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(PaymentMade())).get()
        baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(5)).join()

        // Validate that mocks where called with correct data
        verify(validateOrder).apply(recipeInstanceId, order)
        verify(manufactureGoods).apply(order)
        verify(sendInvoice).apply(customerInfo)
        verify(shipGoods, times(2)).apply(goods, customerInfo)

        // Ensure events appeared
        val expectedEvents = ImmutableList.of(
            "OrderPlaced",
            "OrderValid",
            "CustomerInfoReceived",
            "PaymentMade",
            "GoodsManufactured",
            "GoodsShipped",
            "SendInvoiceExhaustedEvent",
            "RecipeFailureLogged"
        )
        val events = baker.getEventNames(recipeInstanceId).get()
        Assertions.assertEquals(
            HashSet(expectedEvents),
            HashSet(events)
        )

        // We validate that the failure reason is useful for us to analyze
        val failureReason = baker.getIngredient(recipeInstanceId, "failureReason").get().`as`(String::class.java)
        Assertions.assertTrue(failureReason.startsWith("Recipe failed: $recipeInstanceId, with events:"))
        Assertions.assertTrue(failureReason.contains("OrderPlaced"))
        Assertions.assertTrue(failureReason.contains("OrderValid"))
        Assertions.assertTrue(failureReason.contains("CustomerInfoReceived"))
        Assertions.assertTrue(failureReason.contains("PaymentMade"))
        Assertions.assertTrue(failureReason.contains("GoodsManufactured"))
        Assertions.assertTrue(failureReason.contains("GoodsShipped"))
        Assertions.assertTrue(failureReason.contains("SendInvoiceExhaustedEvent"))

        // We can retry the SendInvoice manually
        baker.retryInteraction(recipeInstanceId, "SendInvoice").get()

        val expectedEventsAfterRetry = ImmutableList.of(
            "OrderPlaced",
            "OrderValid",
            "CustomerInfoReceived",
            "PaymentMade",
            "GoodsManufactured",
            "GoodsShipped",
            "SendInvoiceExhaustedEvent",
            "RecipeFailureLogged",
            "InvoiceSent",
            "RecipeSuccessful"
        )

        val eventsAfterRetry = baker.getEventNames(recipeInstanceId).get()

        // Recipe should be successful now.
        Assertions.assertEquals(
            HashSet(expectedEventsAfterRetry),
            HashSet(eventsAfterRetry)
        )
    }
}

