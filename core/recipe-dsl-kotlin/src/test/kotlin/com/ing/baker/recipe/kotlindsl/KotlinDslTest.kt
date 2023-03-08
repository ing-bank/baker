package com.ing.baker.recipe.kotlindsl

import com.example.demo.ScalaExtensions.toJavaIterable
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction as BlockInteraction
import com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure as FireEventAfterFailure
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff as RetryWithIncrementalBackoff
import com.ing.baker.recipe.javadsl.Interaction
import org.junit.Assert.assertEquals
import org.junit.Test
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
                eventWithoutFiringLimit<Events.ShippingAddressReceived>()
            }
            interactions {
                interaction(Interactions.MakePayment::apply)
                interaction(Interactions.ReserveItems::apply)
                interaction(Interactions.ShipItems::apply) {
                    requiredEvents(Interactions.MakePayment.PaymentSuccessful::class)
                }
            }
            defaultFailureStrategy{
                initialDelay(1.0.milliseconds)
                deadline(2.0.hours)
                maxTimeBetweenRetries(3.0.seconds)
            }
        }

        val recipe = convertRecipe(recipeBuilder)

        fun com.ing.baker.recipe.javadsl.Recipe.toIngredientList(i:Int) = getInteractions().get(i).inputIngredients().toJavaIterable().toList().map { it.name() }

        assertEquals(recipe.name(), "Name")

        with(recipe.interactions[0]) {
            assertEquals("MakePayment", name())
            assertEquals(emptySet<String>(), requiredEvents().toJavaIterable().toSet())
            assertEquals(listOf("reservedItems", "paymentInformation"), inputIngredients().toJavaIterable().toList().map { it.name() })
        }

        with(recipe.interactions[1]) {
            assertEquals("ReserveItems", name())
            assertEquals(emptySet<String>(), requiredEvents().toJavaIterable().toSet())
            assertEquals(listOf("items"), inputIngredients().toJavaIterable().toList().map { it.name() })
        }

        with(recipe.interactions[2]) {
            assertEquals("ShipItems", name())
            assertEquals(setOf("PaymentSuccessful"), requiredEvents().toJavaIterable().toSet())
            assertEquals(listOf("shippingAddress", "reservedItems"), inputIngredients().toJavaIterable().toList().map { it.name() })
        }

        with(recipe.events) {
            assertEquals(size, 3)
            assertEquals("OrderPlaced", get(0).name())
            assertEquals("PaymentInformationReceived", get(1).name())
            assertEquals("ShippingAddressReceived", get(2).name())
        }

        with(recipe.defaultFailureStrategy()) {
            when(this){
                is RetryWithIncrementalBackoff -> {
                    assertEquals(1L, this.initialDelay().toMillis())
                    assertEquals(2410, this.maximumRetries())
                    assertEquals(3000L, this.maxTimeBetweenRetries().get().toMillis())
                }
                else -> error("Classname did not match ")
            }
        }
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