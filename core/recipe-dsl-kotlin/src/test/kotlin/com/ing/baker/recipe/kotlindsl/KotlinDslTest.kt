package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.recipe.annotations.RequiresIngredient
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.kotlindsl.JavaInteraction.ItemsReserved
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import scala.Option
import scala.Some
import scala.collection.Seq
import scala.collection.Set
import scala.concurrent.duration.FiniteDuration
import java.util.*
import java.util.concurrent.TimeUnit
import kotlin.time.Duration.Companion.seconds

@OptIn(ExperimentalDsl::class)
class KotlinDslTest {

    @Test
    fun `should convert dsl to recipe`() {
        val recipe = recipe("Name") {
            retentionPeriod = 3.seconds
            eventReceivePeriod = 4.seconds

            defaultFailureStrategy = retryWithIncrementalBackoff {
                initialDelay = 10.0.seconds
                maxTimeBetweenRetries = 3.0.seconds
                backoffFactor = 10.0
                fireRetryExhaustedEvent = "TestEvent1"
                until = deadline(20.0.seconds)
            }

            sensoryEvents {
                eventWithoutFiringLimit<Events.OrderPlaced>()
                event<Events.PaymentInformationReceived>(maxFiringLimit = 5)
                event<Events.ShippingAddressReceived>()
            }

            interaction<Interactions.MakePayment> {
                failureStrategy = fireEventAfterFailure<Events.OrderPlaced>()
            }
            interaction<Interactions.ReserveItems> {
                failureStrategy = fireEventAfterFailure("OrderPlaced")
            }
            interaction<Interactions.ShipItems> {
                failureStrategy = retryWithIncrementalBackoff {
                    initialDelay = 1.0.seconds
                    maxTimeBetweenRetries = 2.0.seconds
                    backoffFactor = 3.0
                    fireRetryExhaustedEvent = "TestEvent1"
                    until = maximumRetries(20)
                }
                requiredEvents {
                    event<Interactions.MakePayment.PaymentSuccessful>()
                }
            }
            interaction<Interactions.ShipItems> {
                name = "foo"
                maximumInteractionCount = 10

                preDefinedIngredients {
                    "foo" to "val"
                    "bar" to true
                }

                requiredEvents {
                    event<Interactions.MakePayment.PaymentSuccessful>()
                    event("myEvent")
                }

                requiredOneOfEvents {
                    event<Ingredients.PaymentInformation>()
                    event("SomeEvent")
                }

                transformEvent<Char>("foo")

                transformEvent<Boolean>(newName = "AnotherBoolean") {
                    "foo" to "bar"
                    "this" to "that"
                }

                ingredientNameOverrides {
                    "foo" to "yolo"
                    "bar" to "krakaka"
                }
            }
        }

        assertEquals("Name", recipe.name())
        assertEquals(FiniteDuration(3000000000, TimeUnit.NANOSECONDS), recipe.retentionPeriod().get())
        assertEquals(FiniteDuration(4000000000, TimeUnit.NANOSECONDS), recipe.eventReceivePeriod().get())

        with(recipe.interactions().toList().apply(0)) {
            assertEquals("MakePayment", name())

            assertEquals(0, requiredEvents().size())

            assertEquals(2, inputIngredients().size())
            assertEquals("reservedItems", inputIngredients().toList().apply(0).name())
            assertEquals("paymentInformation", inputIngredients().toList().apply(1).name())

            with(failureStrategy().get()) {
                when (this) {
                    is InteractionFailureStrategy.FireEventAfterFailure -> {
                        assertEquals("OrderPlaced", eventName().get())
                    }

                    else -> error("Classname did not match ")
                }
            }
        }

        with(recipe.interactions().toList().apply(1)) {
            assertEquals("ReserveItems", name())

            assertEquals(0, requiredEvents().size())

            assertEquals(1, inputIngredients().size())
            assertEquals("items", inputIngredients().toList().apply(0).name())

            with(failureStrategy().get()) {
                when (this) {
                    is InteractionFailureStrategy.FireEventAfterFailure -> {
                        assertEquals("OrderPlaced", eventName().get())
                    }

                    else -> error("Classname did not match ")
                }
            }
        }

        with(recipe.interactions().toList().apply(2)) {
            assertEquals("ShipItems", name())

            assertEquals("ShippingConfirmed", output().apply(0).name())
            assertEquals(0, output().apply(0).providedIngredients().size())

            assertEquals(1, requiredEvents().size())
            assertEquals("PaymentSuccessful", requiredEvents().toList().apply(0))

            assertEquals(2, inputIngredients().size())
            assertEquals("shippingAddress", inputIngredients().toList().apply(0).name())
            assertEquals("reservedItems", inputIngredients().toList().apply(1).name())

            with(failureStrategy().get()) {
                when (this) {
                    is InteractionFailureStrategy.RetryWithIncrementalBackoff -> {
                        assertEquals(1L, initialDelay().toSeconds())
                        assertEquals(20, maximumRetries())
                        assertEquals(2000L, maxTimeBetweenRetries().get().toMillis())
                        assertEquals("TestEvent1", fireRetryExhaustedEvent().get().get())
                        assertEquals(3.0, backoffFactor(), 0.0)
                    }

                    else -> error("Classname did not match ")
                }
            }
        }

        with(recipe.interactions().toList().apply(3)) {
            assertEquals("foo", name())
            assertEquals(10, maximumInteractionCount().get())

            assertEquals(2, requiredEvents().size())
            assertEquals("PaymentSuccessful", requiredEvents().toList().apply(0))
            assertEquals("myEvent", requiredEvents().toList().apply(1))

            assertEquals(2, inputIngredients().size())
            assertEquals("shippingAddress", inputIngredients().toList().apply(0).name())
            assertEquals("reservedItems", inputIngredients().toList().apply(1).name())

            assertEquals(2, predefinedIngredients().size())
            assertEquals(
                "val",
                (predefinedIngredients().get("foo").get() as com.ing.baker.types.PrimitiveValue).value()
            )
            assertEquals(true, (predefinedIngredients().get("bar").get() as com.ing.baker.types.PrimitiveValue).value())

            assertEquals(2, requiredEvents().size())
            assertEquals("PaymentSuccessful", requiredEvents().get(0))
            assertEquals("myEvent", requiredEvents().get(1))

            assertEquals(1, requiredOneOfEvents().size())
            assertEquals(2, requiredOneOfEvents().get(0).size())
            assertEquals("PaymentInformation", requiredOneOfEvents().get(0).get(0))
            assertEquals("SomeEvent", requiredOneOfEvents().get(0).get(1))

            assertEquals(2, eventOutputTransformers().size())
            assertEquals(Event("Char", listOf(), Optional.empty()), eventOutputTransformers().toList().get(0)._1)
            assertEquals(EventOutputTransformer("foo", emptyMap()), eventOutputTransformers().toList().get(0)._2)
            assertEquals(Event("Boolean", listOf(), Optional.empty()), eventOutputTransformers().toList().get(1)._1)
            assertEquals(
                EventOutputTransformer("AnotherBoolean", mapOf("foo" to "bar", "this" to "that")),
                eventOutputTransformers().toList().get(1)._2
            )

            assertEquals(2, overriddenIngredientNames().size())
            assertEquals("yolo", overriddenIngredientNames().get("foo").get())
            assertEquals("krakaka", overriddenIngredientNames().get("bar").get())

            assertTrue(failureStrategy().isEmpty)
        }

        with(recipe.sensoryEvents()) {
            assertEquals(this.size(), 3)
            assertEquals("OrderPlaced", this.toList().apply(0).name())
            assertEquals("PaymentInformationReceived", this.toList().apply(1).name())
            assertEquals("ShippingAddressReceived", this.toList().apply(2).name())
        }

        with(recipe.defaultFailureStrategy()) {
            when (this) {
                is InteractionFailureStrategy.RetryWithIncrementalBackoff -> {
                    assertEquals(10L, this.initialDelay().toSeconds())
                    assertEquals(4, this.maximumRetries())
                    assertEquals(3000L, this.maxTimeBetweenRetries().get().toMillis())
                    assertEquals("TestEvent1", fireRetryExhaustedEvent().get().get())
                    assertEquals(10.0, this.backoffFactor(), 0.0)
                }

                else -> error("Classname did not match ")
            }
        }
    }

    @Test
    fun `create a recipe without any configuration`() {
        val recipe = recipe("NameNoProps")

        with(recipe) {
            assertEquals("NameNoProps", name())
            assertEquals(Option.empty<FiniteDuration>(), retentionPeriod())
            assertEquals(Option.empty<FiniteDuration>(), eventReceivePeriod())
            assertEquals(BlockInteraction::class.java, defaultFailureStrategy().javaClass)
            assertTrue(sensoryEvents().isEmpty)
            assertTrue(interactions().isEmpty)
        }
    }

    @Test
    fun `create a recipe with sensory events`() {
        val recipe = recipe("recipe with sensory events") {
            sensoryEvents {
                eventWithoutFiringLimit<Events.One>()
                event<Events.Two>(maxFiringLimit = 5)
                event<Events.Three>()
            }
        }

        with(recipe) {
            assertEquals("recipe with sensory events", name())
            assertEquals(3, sensoryEvents().size())

            with(sensoryEvents().get(0)) {
                assertEquals("One", name())
                assertEquals(Option.empty<Int>(), maxFiringLimit())
                assertEquals(1, providedIngredients().size())
                assertEquals("flag", providedIngredients().get(0).name())
                assertEquals("Bool", providedIngredients().get(0).ingredientType().toString())
            }
            with(sensoryEvents().get(1)) {
                assertEquals("Two", name())
                assertEquals(Some(5), maxFiringLimit())
                assertEquals(1, providedIngredients().size())
                assertEquals("text", providedIngredients().get(0).name())
                assertEquals("CharArray", providedIngredients().get(0).ingredientType().toString())
            }
            with(sensoryEvents().get(2)) {
                assertEquals("Three", name())
                assertEquals(Some(1), maxFiringLimit())
                assertEquals(1, providedIngredients().size())
                assertEquals("number", providedIngredients().get(0).name())
                assertEquals("Int32", providedIngredients().get(0).ingredientType().toString())
            }
        }
    }

    @Test
    fun `create a recipe with interactions that use annotations`() {
        val recipe = recipe("recipe with interactions that use annotations") {
            interaction<JavaInteraction>()
            interaction<KotlinInteractionWithAnnotations>()
        }

        with(recipe.interactions().toList().apply(0)) {
            assertEquals("JavaInteraction", name())

            assertEquals(2, inputIngredients().size())
            assertEquals(inputIngredients().toList().apply(0).name(), "orderId")
            assertEquals(inputIngredients().toList().apply(1).name(), "items")

            assertEquals(2, output().size())
            with(output().toList().apply(0)) {
                assertEquals("ItemsReserved", name())
                assertEquals(1, providedIngredients().size())
                assertEquals("reservedItems", providedIngredients().toList().apply(0).name())
            }
            with(output().toList().apply(1)) {
                assertEquals("OrderHadUnavailableItems", name())
                assertEquals(1, providedIngredients().size())
                assertEquals("unavailableItems", providedIngredients().toList().apply(0).name())
            }
        }

        with(recipe.interactions().toList().apply(1)) {
            assertEquals("KotlinInteractionWithAnnotations", name())

            assertEquals(1, inputIngredients().size())
            assertEquals(inputIngredients().toList().apply(0).name(), "id")

            assertEquals(2, output().size())
            with(output().toList().apply(0)) {
                assertEquals("Person", name())
                assertEquals(2, providedIngredients().size())
                assertEquals("name", providedIngredients().toList().apply(0).name())
                assertEquals("age", providedIngredients().toList().apply(1).name())
            }
            with(output().toList().apply(1)) {
                assertEquals("Error", name())
                assertEquals(1, providedIngredients().size())
                assertEquals("reason", providedIngredients().toList().apply(0).name())
            }
        }
    }

    @Test
    fun `create a recipe with checkpoint events`() {
        val recipe = recipe("RecipeWithCheckpointEvent") {
            checkpointEvent("Success") {
                requiredEvents {
                    event<Interactions.MakePayment.PaymentSuccessful>()
                    event("myEvent")
                }

                requiredOneOfEvents {
                    event<Ingredients.PaymentInformation>()
                    event("SomeEvent")
                }
            }
        }

        with(recipe) {
            assertEquals("RecipeWithCheckpointEvent", name())
            assertEquals(Option.empty<FiniteDuration>(), retentionPeriod())
            assertEquals(Option.empty<FiniteDuration>(), eventReceivePeriod())
            assertEquals(BlockInteraction::class.java, defaultFailureStrategy().javaClass)
            assertEquals(1, checkpointEvents().size())
            assertEquals("Success", checkpointEvents().get(0).name())
            assertEquals(2, checkpointEvents().get(0).requiredEvents().size())
            assertEquals("PaymentSuccessful", checkpointEvents().get(0).requiredEvents().get(0))
            assertEquals("myEvent", checkpointEvents().get(0).requiredEvents().get(1))
            assertEquals(1, checkpointEvents().get(0).requiredOneOfEvents().size())
            assertEquals(2, checkpointEvents().get(0).requiredOneOfEvents().get(0).size())
            assertEquals("PaymentInformation", checkpointEvents().get(0).requiredOneOfEvents().get(0).get(0))
            assertEquals("SomeEvent", checkpointEvents().get(0).requiredOneOfEvents().get(0).get(1))
            assertTrue(sensoryEvents().isEmpty)
            assertTrue(interactions().isEmpty)
        }
    }

    @Test
    fun `create a recipe with sieve events`() {
        val recipe = recipe("RecipeWithSieve") {
            interaction<Interactions.MakePayment> {
                failureStrategy = fireEventAfterFailure<Events.OrderPlaced>()
            }
            interaction<Interactions.ReserveItems> {
                failureStrategy = fireEventAfterFailure("OrderPlaced")
            }

            ingredient("extractDate"){ reservedItems: Ingredients.ReservedItems ->  reservedItems.date }
        }

        with(recipe) {
            assertEquals("RecipeWithSieve", name())
            assertEquals(Option.empty<FiniteDuration>(), retentionPeriod())
            assertEquals(Option.empty<FiniteDuration>(), eventReceivePeriod())
            assertEquals(BlockInteraction::class.java, defaultFailureStrategy().javaClass)
            assertEquals(2, interactions().size())
            assertEquals("MakePayment", interactions().get(0).name())
            assertEquals("ReserveItems", interactions().get(1).name())
            assertEquals(1, sieves().size())
            assertEquals("extractDate", sieves().get(0).name())
            assertEquals(1, sieves().get(0).inputIngredients().size())
            assertEquals("reservedItems", sieves().get(0).inputIngredients().get(0).name())
            assertEquals(1, sieves().get(0).output().size())
            assertEquals("\$SieveEvent\$extractDate", sieves().get(0).output().get(0).name())
        }
    }

    @Test
    fun `create a recipe with subrecipe`() {
        val fulfillment = recipe("Fulfillment") {
            interaction<Interactions.ReserveItems> {
                failureStrategy = fireEventAfterFailure("OrderPlaced")
            }
            interaction<Interactions.ShipItems> {
                failureStrategy = retryWithIncrementalBackoff {
                    initialDelay = 1.0.seconds
                    maxTimeBetweenRetries = 2.0.seconds
                    backoffFactor = 3.0
                    fireRetryExhaustedEvent = "TestEvent1"
                    until = maximumRetries(20)
                }
                requiredEvents {
                    event<Interactions.MakePayment.PaymentSuccessful>()
                }
            }
        }

        val webshop = recipe("Webshop") {

            sensoryEvents {
                eventWithoutFiringLimit<Events.OrderPlaced>()
                event<Events.PaymentInformationReceived>(maxFiringLimit = 5)
                event<Events.ShippingAddressReceived>()
            }

            subRecipe(fulfillment)

            interaction<Interactions.MakePayment> {
                failureStrategy = fireEventAfterFailure<Events.OrderPlaced>()
            }

        }

        with(webshop) {
            assertEquals("Webshop", name())
            assertEquals(Option.empty<FiniteDuration>(), retentionPeriod())
            assertEquals(Option.empty<FiniteDuration>(), eventReceivePeriod())
            assertEquals(BlockInteraction::class.java, defaultFailureStrategy().javaClass)
            assertEquals(1, subRecipes().size())
            assertEquals("Fulfillment", subRecipes().get(0).name())
        }
    }

    @Test
    fun `transformEvent should work for Java classes`() {
        val recipe = recipe("java transform event") {
            interaction<JavaInteraction> {
                transformEvent<ItemsReserved>(newName = "ItemsReservedNew") {
                    "reservedItems" to "reservedItemsNew"
                }
            }
        }

        with(recipe.interactions().apply(0)) {
            assertEquals(1, eventOutputTransformers().size())
            assertEquals("ItemsReserved", eventOutputTransformers().toList().get(0)._1.name())
            assertEquals(
                EventOutputTransformer("ItemsReservedNew", mapOf("reservedItems" to "reservedItemsNew")),
                eventOutputTransformers().toList().get(0)._2
            )
        }
    }

    @Test
    fun `a Kotlin interaction without annotations with a generic ingredient container of which the elements are Java types`() {
        val recipe = recipe("reproduce") {
            interaction<GenericIngredientContainerWithJavaElements>()
        }

        with(recipe.interactions().apply(0)) {
            assertEquals(4, inputIngredients().size())
            assertEquals("metaData", inputIngredients().toList().apply(0).name())
            assertEquals("CharArray", inputIngredients().toList().apply(0).ingredientType().toString())
            assertEquals("agreements", inputIngredients().toList().apply(1).name())
            assertEquals(
                "List[Record(name: CharArray, id: Int64)]",
                inputIngredients().toList().apply(1).ingredientType().toString()
            )
            assertEquals("uniqueAgreements", inputIngredients().toList().apply(2).name())
            assertEquals(
                "List[Record(name: CharArray, id: Int64)]",
                inputIngredients().toList().apply(2).ingredientType().toString()
            )
            assertEquals("mapOfAgreements", inputIngredients().toList().apply(3).name())
            assertEquals(
                "Map[Record(name: CharArray, id: Int64)]",
                inputIngredients().toList().apply(3).ingredientType().toString()
            )
        }
    }

    @Test
    fun `nested sealed classes`() {

        val recipe = recipe("RecipeWithNestedSealedClasses") {
            interaction<ApiInteraction>()
        }

        with(recipe) {
            assertEquals("RecipeWithNestedSealedClasses", name())
            assertEquals(1, interactions().size())
        }

        with(recipe.interactions().toList().apply(0)) {
            assertEquals("ApiInteraction", name())

            assertEquals(1, inputIngredients().size())
            assertEquals("reservedItems", inputIngredients().toList().apply(0).name())

            assertEquals(2, output().size())
            assertEquals("ResponseSuccessful", output().toList().apply(0).name())
            assertEquals("ResponseFailed", output().toList().apply(1).name())
        }
    }

    object Events {
        class OrderPlaced(val items: List<Ingredients.Item>)
        class PaymentInformationReceived(val paymentInformation: Ingredients.PaymentInformation)
        class ShippingAddressReceived(val shippingAddress: Ingredients.ShippingAddress)

        class One(val flag: Boolean)
        class Two(val text: String)
        class Three(val number: Int)
    }

    object Ingredients {
        data class Item(val itemId: String)
        data class PaymentInformation(val info: String)
        data class ReservedItems(val items: List<Item>, val date: String)
        data class ShippingAddress(val address: String)
    }

    object Interactions {

        interface MakePayment : Interaction {
            sealed interface MakePaymentOutcome
            object PaymentSuccessful : MakePaymentOutcome
            object PaymentFailed : MakePaymentOutcome

            fun apply(
                reservedItems: Ingredients.ReservedItems,
                paymentInformation: Ingredients.PaymentInformation
            ): MakePaymentOutcome
        }

        interface ShipItems : Interaction {
            object ShippingConfirmed

            fun apply(
                shippingAddress: Ingredients.ShippingAddress,
                reservedItems: Ingredients.ReservedItems
            ): ShippingConfirmed
        }

        interface ReserveItems : Interaction {
            sealed interface ReserveItemsOutcome
            class OrderHadUnavailableItems(val unavailableItems: List<Ingredients.Item>) : ReserveItemsOutcome
            class ItemsReserved(val reservedItems: Ingredients.ReservedItems) : ReserveItemsOutcome

            fun apply(items: List<Ingredients.Item>): ReserveItemsOutcome
        }
    }

    interface GenericIngredientContainerWithJavaElements : Interaction {
        class Result

        fun apply(
            metaData: String,
            agreements: List<ProductAgreement>,
            uniqueAgreements: kotlin.collections.Set<ProductAgreement>,
            mapOfAgreements: Map<Long, ProductAgreement>
        ): Result
    }

    interface ApiInteraction : Interaction {
        sealed interface Response
        sealed interface Response200 : Response
        sealed interface Response500 : Response
        class ResponseSuccessful : Response200
        class ResponseFailed : Response500

        fun apply(
            reservedItems: Ingredients.ReservedItems,
        ): Response
    }

    interface KotlinInteractionWithAnnotations : Interaction {
        interface Outcome
        data class Person(val name: String, val age: Int) : Outcome
        data class Error(val reason: String) : Outcome

        @FiresEvent(oneOf = [Person::class, Error::class])
        fun apply(
            @RequiresIngredient("id") id: String,
        ): Outcome
    }

    private fun <T> Seq<T>.get(index: Int): T = apply(index)
    private fun <T> Set<T>.get(index: Int): T = toList().apply(index)
}