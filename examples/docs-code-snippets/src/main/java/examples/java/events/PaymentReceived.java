package examples.java.events;

import java.math.BigDecimal;

public record PaymentReceived(
    String orderId,
    BigDecimal amount,
    String currency
) {
}
