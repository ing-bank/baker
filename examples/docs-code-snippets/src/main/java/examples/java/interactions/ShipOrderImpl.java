package examples.java.interactions;

import examples.java.ingredients.Address;

public class ShipOrderImpl implements ShipOrder {
    @Override
    public Success apply(String orderId, Address address) {
        System.out.printf("Shipping order %s to %s", orderId, address);
        return new ShipOrder.Success();
    }
}
