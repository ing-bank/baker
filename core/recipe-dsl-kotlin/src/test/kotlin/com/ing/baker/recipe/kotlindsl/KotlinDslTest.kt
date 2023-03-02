package com.ing.baker.recipe.kotlindsl

import com.example.demo.ScalaExtensions.toJavaIterable
import com.ing.baker.recipe.javadsl.Interaction
import org.junit.Assert.assertEquals
import org.junit.Test

class KotlinDslTest {

    @Test
    fun `should convert dsl to recipe`() {
        val recipeBuilder = recipe("Name") {
            interactions {
                interaction(Interactions.MakePayment::apply)
                interaction(Interactions.ReserveItems::apply)
                interaction(Interactions.ShipItems::apply) {
                    requiredEvents(Interactions.MakePayment.PaymentSuccessful::class)
                }
            }
            sensoryEvents(
                Events.OrderPlaced::class,
                Events.PaymentInformationReceived::class,
                Events.ShippingAddressReceived::class
            )
        }

        val recipe = convertRecipe(recipeBuilder)

        assertEquals(recipe.name(), "Name")
        assertEquals(
            recipe.getInteractions().get(0).inputIngredients().toJavaIterable().toList().map { it.name() },
            listOf("reservedItems", "paymentInformation")
        )

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