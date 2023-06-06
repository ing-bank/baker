package examples.java.interactions;

import java.util.List;

public class CancelOrderImpl implements CancelOrder {
    @Override
    public OrderCancelled apply(String orderId, List<String> unavailableProductIds) {
        System.out.printf("Canceling order %s. The following products are unavailable: %s", orderId, unavailableProductIds);
        return new OrderCancelled();
    }
}
