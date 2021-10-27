package webshop.simple.ingredients;

import java.util.List;

public class ShippingOrder{

    private List<Item> items;
    private byte[] data;
    private ShippingAddress shippingAddress;

    public ShippingOrder(List<Item> items, byte[] data, ShippingAddress shippingAddress) {
        this.items = items;
        this.data = data;
        this.shippingAddress = shippingAddress;
    }

    public List<Item> getItems() {
        return items;
    }

    public byte[] getData() {
        return data;
    }

    public ShippingAddress getShippingAddress() {
        return shippingAddress;
    }
}
