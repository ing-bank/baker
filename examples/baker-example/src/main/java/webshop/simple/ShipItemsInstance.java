package webshop.simple;

import webshop.simple.ingredients.ShippingOrder;

public class ShipItemsInstance implements ShipItems {
    @Override
    public ShippingConfirmed apply(ShippingOrder shippingOrder) {
        return new ShippingConfirmed();
    }
}
