package examples.java.interactions;

import java.util.List;

public class CheckStockImpl implements CheckStock {

    @Override
    public Outcome apply(String orderId, List<String> productIds) {
        System.out.printf("Checking stock for order: %s and products: %s%n", orderId, productIds);

        int random = (int) (Math.random() * (1000 - 1)) + 1;
        if (random < 500) {
            return new SufficientStock();
        } else {
            return new OrderHasUnavailableItems(productIds);
        }
    }
}
