package com.ing.baker.runtime.inmemory.recipe

import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.inmemory.recipe.ManufactureGoods.GoodsManufactured
import com.ing.baker.runtime.inmemory.recipe.SendInvoice.InvoiceSent
import com.ing.baker.runtime.inmemory.recipe.ShipGoods.GoodsShipped
import com.ing.baker.runtime.inmemory.recipe.ValidateOrder.OrderValid
import com.ing.baker.runtime.inmemory.recipe.ValidateOrder.ValidateOrderOutcome
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.util.UUID

interface LogRecipeFailed : Interaction {

    data class RecipeFailureLogged(val failureReason: String)

    fun apply(
        recipeInstanceId: String,
        RecipeInstanceEventList: MutableList<String>
    ): RecipeFailureLogged
}

class LogRecipeFailedImpl : LogRecipeFailed {

    companion object {
        private val log: Logger = LoggerFactory.getLogger(LogRecipeFailed::class.java)
    }

    override fun apply(
        recipeInstanceId: String,
        RecipeInstanceEventList: MutableList<String>
    ): LogRecipeFailed.RecipeFailureLogged {

        val failureMessage = "Recipe failed: $recipeInstanceId, with events: $RecipeInstanceEventList"
        log.error(failureMessage)
        return LogRecipeFailed.RecipeFailureLogged(failureMessage)
    }
}

interface ManufactureGoods : Interaction {
    companion object {
        // Adding a name variable towards you interaction set the name of the interaction.
        // If not set the class name is used.
        const val name = "ManufactorGoodsNameFromField"
    }
    data class GoodsManufactured(val goods: String)

    fun apply(order: String): GoodsManufactured
}

class ManufactureGoodsImpl : ManufactureGoods {
    override fun apply(order: String): GoodsManufactured {
        //Call system that manufactures the goods
        return GoodsManufactured(UUID.randomUUID().toString())
    }
}

interface SendInvoice : Interaction {
    class InvoiceSent

    fun apply(customerInfo: CustomerInfo): InvoiceSent
}

class SendInvoiceImpl : SendInvoice {
    override fun apply(customerInfo: CustomerInfo): InvoiceSent {
        //Code that calls a system that sends an invoice
        return InvoiceSent()
    }
}

interface ShipGoods : Interaction {
    data class GoodsShipped(val trackingId: String)

    fun apply(goods: String, customerInfo: CustomerInfo): GoodsShipped
}

class ShipGoodsImpl : ShipGoods {
    override fun apply(goods: String, customerInfo: CustomerInfo): GoodsShipped {
        //Call system that ships goods and returns a trackingId
        return GoodsShipped(UUID.randomUUID().toString())
    }
}

@Suppress("CanSealedSubClassBeObject") // Not possible at the moment as Baker does not support Kotlin object
interface ValidateOrder : Interaction {
    sealed interface ValidateOrderOutcome
    class OrderInvalid : ValidateOrderOutcome
    class OrderValid : ValidateOrderOutcome

    fun apply(recipeInstanceId: String, order: String): ValidateOrderOutcome
}

class ValidateOrderImpl() : ValidateOrder {
    override fun apply(recipeInstanceId: String, order: String): ValidateOrderOutcome {
        return OrderValid()
    }
}
