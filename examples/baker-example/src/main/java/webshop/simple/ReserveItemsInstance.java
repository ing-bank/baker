package webshop.simple;

import webshop.simple.ingredients.Item;
import webshop.simple.ingredients.ReservedItems;

import java.util.List;
import java.util.Random;

public class ReserveItemsInstance implements ReserveItems {

    @Override
    public ReserveItems.ReserveItemsOutcome apply(String id, List<Item> items) {
        byte[] b = new byte[20];
        new Random().nextBytes(b);
        return new ReserveItems.ItemsReserved(new ReservedItems(items, b));
    }
}
