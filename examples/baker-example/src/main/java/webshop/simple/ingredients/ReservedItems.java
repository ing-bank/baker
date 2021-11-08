package webshop.simple.ingredients;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.List;

public class ReservedItems {

    private List<Item> items;
    private byte[] date;

    public ReservedItems(List<Item> items, byte[] date) {
        this.items = items;
        this.date = date;
    }

    public List<Item> getItems() {
        return items;
    }

    public byte[] getDate() {
        return date;
    }
}
