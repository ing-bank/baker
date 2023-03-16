package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction as BlockInteraction
import com.ing.baker.recipe.javadsl.Interaction
import org.junit.Assert.assertEquals
import org.junit.Test
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

class KotlinDslTest {

    @Test
    fun `should convert dsl to recipe`() {
        val recipeBuilder = recipe("Name") {
            sensoryEvents {
                event<Events.OrderPlaced>()
                event<Events.PaymentInformationReceived>(maxFiringLimit = 5)
                event<Events.ShippingAddressReceived>(maxFiringLimit = 1)
            }
            interactions {
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
                    preDefinedIngredients = setOf(
                        "foo" to "bar"
                    )

                    requiredEvents {
                        event<Interactions.MakePayment.PaymentSuccessful>()
                        event("myEvent")
                    }

                    requiredOneOfEvents {
                        event<Ingredients.PaymentInformation>()
                        event("SomeEvent")
                    }

                    transformEvent<Char>("foo")

                    transformEvent<Boolean>(
                        to = "AnotherBoolean",
                        ingredientRenames = mapOf(
                            "foo" to "bar",
                            "this" to "that"
                        )
                    )

                    requiredEvents(Interactions.MakePayment.PaymentSuccessful::class)

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

        assertEquals(recipe.name(), "Name")

        with(recipe.interactions().toList().apply(0)) {
            assertEquals("MakePayment", name())

            assertEquals(0, requiredEvents().size())

            assertEquals(2, inputIngredients().size())
            assertEquals("paymentInformation", inputIngredients().toList().apply(0).name())
            assertEquals("reservedItems", inputIngredients().toList().apply(1).name())
        }

        with(recipe.interactions().toList().apply(1)) {
            assertEquals("ReserveItems", name())

            assertEquals(0, requiredEvents().size())

            assertEquals(1, inputIngredients().size())
            assertEquals("items", inputIngredients().toList().apply(0).name())

            with(failureStrategy().get()) {
                when(this){
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

        with(recipe.interactions().toList().apply(2)) {
            assertEquals("ShipItems", name())

            assertEquals(1, requiredEvents().size())
            assertEquals("PaymentSuccessful", requiredEvents().toList().apply(0))

            assertEquals(2, inputIngredients().size())
            assertEquals("shippingAddress", inputIngredients().toList().apply(0).name())
            assertEquals("reservedItems", inputIngredients().toList().apply(1).name())
        }

        with(recipe.sensoryEvents()) {
            assertEquals(this.size(), 3)
            assertEquals("OrderPlaced", this.toList().apply(0).name())
            assertEquals("PaymentInformationReceived", this.toList().apply(1).name())
            assertEquals("ShippingAddressReceived",this.toList().apply(2).name())
        }

        with(recipe.defaultFailureStrategy()) {
            when(this){
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
    fun `should convert to recipe without properties`(){
        val recipeBuilder = recipe("NameNoProps")
        val recipe = convertRecipe(recipeBuilder)
        assertEquals(BlockInteraction::class.java, recipe.defaultFailureStrategy().javaClass)
    }

    object Events {
        class OrderPlaced(val items: List<Ingredients.Item>)
        class PaymentInformationReceived(val paymentInformation: Ingredients.PaymentInformation)
        class ShippingAddressReceived(val shippingAddress: Ingredients.ShippingAddress)
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


}