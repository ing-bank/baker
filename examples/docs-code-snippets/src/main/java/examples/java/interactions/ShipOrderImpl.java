package examples.java.interactions;

import examples.java.ingredients.Address;

public class ShipOrderImpl implements ShipOrder {
    @Override
    public OrderShipped apply(String orderId, Address address) {
        System.out.printf("Shipping order %s to %s", orderId, address);
        return new OrderShipped();
    }
}
