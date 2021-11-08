package webshop.simple;

import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;

public class ShipItemsInstance implements ShipItems {
    @Override
    public ShippingConfirmed apply(ShippingAddress shippingAddress, ReservedItems reservedItems) {
        return new ShippingConfirmed();
    }
}
