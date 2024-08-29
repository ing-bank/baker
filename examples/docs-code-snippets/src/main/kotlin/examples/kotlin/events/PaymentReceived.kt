package examples.kotlin.events

import java.math.BigDecimal

data class PaymentReceived(
    val orderId: String,
    val amount: BigDecimal,
    val currency: String
)