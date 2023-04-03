package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.javadsl.Interaction
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
            assertEquals("val", (predefinedIngredients().get("foo").get() as com.ing.baker.types.PrimitiveValue).value())
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
            assertEquals(EventOutputTransformer("AnotherBoolean", mapOf("foo" to "bar", "this" to "that")), eventOutputTransformers().toList().get(1)._2)

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
            class PaymentSuccessful : MakePaymentOutcome
            class PaymentFailed : MakePaymentOutcome

            fun apply(
                reservedItems: Ingredients.ReservedItems,
                paymentInformation: Ingredients.PaymentInformation
            ): MakePaymentOutcome
        }

        interface ShipItems : Interaction {
            class ShippingConfirmed

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

    private fun <T> Seq<T>.get(index: Int): T = apply(index)
    private fun <T> Set<T>.get(index: Int): T = toList().apply(index)
    private fun <T> Set<T>.firstElement(): T = get(0)
    private fun <T> Set<T>.secondElement(): T = get(1)

}