package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction as BlockInteraction
import com.ing.baker.recipe.javadsl.Interaction
import org.junit.Assert.assertEquals
import org.junit.Test
import scala.Option
import scala.Some
import scala.collection.Seq
import scala.collection.Set
import scala.concurrent.duration.FiniteDuration
import java.util.concurrent.TimeUnit
import kotlin.time.Duration.Companion.seconds

class KotlinDslTest {

    @Test
    fun `should convert dsl to recipe`() {
        val recipeBuilder = recipe("Name") {
            retentionPeriod = 3.seconds
            eventReceivePeriod = 4.seconds
            sensoryEvents {
                event<Events.OrderPlaced>()
                event<Events.PaymentInformationReceived>(maxFiringLimit = 5)
                event<Events.ShippingAddressReceived>(maxFiringLimit = 1)
            }

            interaction(Interactions.MakePayment::apply)
            interaction(Interactions.ReserveItems::apply)
            interaction(Interactions.ShipItems::apply) {
                requiredEvents {
                    event<Interactions.MakePayment.PaymentSuccessful>()
                }
                failureStrategy {
                    initialDelay = 1.0.seconds
                    maxTimeBetweenRetries = 2.0.seconds
                    backoffFactor = 3.0
                    fireRetryExhaustedEvent = "TestEvent1"
                    until = maximumRetries(20)
                }
            }
            interaction(Interactions.ShipItems::apply) {
                name = "foo"
                maximumInteractionCount = 10

                preDefinedIngredients {
                    "foo" to "bar"
                    "blah" to true
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

            defaultFailureStrategy {
                initialDelay = 10.0.seconds
                maxTimeBetweenRetries = 3.0.seconds
                backoffFactor = 10.0
                fireRetryExhaustedEvent = "TestEvent1"
                until = deadline(20.0.seconds)
            }
        }

        val recipe = convertRecipe(recipeBuilder)

        assertEquals("Name", recipe.name())
        assertEquals(Option.apply(FiniteDuration(3000000000, TimeUnit.NANOSECONDS)), recipe.retentionPeriod())
        assertEquals(Option.apply(FiniteDuration(4000000000, TimeUnit.NANOSECONDS)), recipe.eventReceivePeriod())

        with(recipe.interactions().toList().apply(0)) {
            assertEquals("MakePayment", name())

            assertEquals(0, requiredEvents().size())

            assertEquals(2, inputIngredients().size())
            assertEquals("reservedItems", inputIngredients().toList().apply(0).name())
            assertEquals("paymentInformation", inputIngredients().toList().apply(1).name())
        }

        with(recipe.interactions().toList().apply(1)) {
            assertEquals("ReserveItems", name())

            assertEquals(0, requiredEvents().size())

            assertEquals(1, inputIngredients().size())
            assertEquals("items", inputIngredients().toList().apply(0).name())
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
                        assertEquals(1L, this.initialDelay().toSeconds())
                        assertEquals(20, this.maximumRetries())
                        assertEquals(2000L, this.maxTimeBetweenRetries().get().toMillis())
                        assertEquals(3.0, this.backoffFactor(), 0.0)
                    }

                    else -> error("Classname did not match ")
                }
            }
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
                    assertEquals(10.0, this.backoffFactor(), 0.0)
                }

                else -> error("Classname did not match ")
            }
        }
    }

    @Test
    fun `create a recipe without any configuration`() {
        val recipeBuilder = recipe("NameNoProps")
        val recipe = convertRecipe(recipeBuilder)
        assertEquals(BlockInteraction::class.java, recipe.defaultFailureStrategy().javaClass)
    }

    @Test
    fun `create a recipe with sensory events`() {
        val recipeBuilder = recipe("recipe with sensory events") {
            sensoryEvents {
                event<Events.One>()
                event<Events.Two>(maxFiringLimit = 5)
            }
        }

        val recipe = convertRecipe(recipeBuilder)

        assertEquals("recipe with sensory events", recipe.name())

        with(recipe.sensoryEvents()) {
            assertEquals(2, size())

            with(firstElement()) {
                assertEquals("One", name())
                assertEquals(Option.empty<Int>(), maxFiringLimit())
                assertEquals(1, providedIngredients().size())
                assertEquals("flag", providedIngredients().get(0).name())
                assertEquals("Bool", providedIngredients().get(0).ingredientType().toString())
            }

            with(secondElement()) {
                assertEquals("Two", name())
                assertEquals(Some(5), maxFiringLimit())
                assertEquals(1, providedIngredients().size())
                assertEquals("text", providedIngredients().get(0).name())
                assertEquals("CharArray", providedIngredients().get(0).ingredientType().toString())
            }
        }
    }

    object Events {
        class OrderPlaced(val items: List<Ingredients.Item>)
        class PaymentInformationReceived(val paymentInformation: Ingredients.PaymentInformation)
        class ShippingAddressReceived(val shippingAddress: Ingredients.ShippingAddress)

        class One(val flag: Boolean)
        class Two(val text: String)
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