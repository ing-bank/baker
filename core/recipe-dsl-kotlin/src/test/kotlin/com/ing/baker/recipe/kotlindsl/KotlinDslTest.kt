package com.ing.baker.recipe.kotlindsl

import org.jetbrains.annotations.TestOnly
import org.junit.Test
import org.junit.Assert.assertEquals

import com.ing.baker.recipe.javadsl.Interaction

class KotlinDslTest {
    @Test
    fun `should convert dsl to recipe`() {
        val recipe = recipe {
            name = "Recipe"
            interactions(
                interaction {
                    func(
                        Interactions.MakePayment::apply
                    )
                },
                interaction {
                    func(
                        Interactions.ReserveItems::apply
                    )
                },
                interaction {
                    func(
                        Interactions.ShipItems::apply
                    )
                    requiredEvents(
                        Interactions.MakePayment.PaymentSuccessful::class
                    )
                }
            )
            sensoryEvents(
                Events.OrderPlaced::class,
                Events.PaymentInformationReceived::class,
                Events.ShippingAddressReceived::class
            )
        }

        assertEquals(recipe.name, "Recipe")
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