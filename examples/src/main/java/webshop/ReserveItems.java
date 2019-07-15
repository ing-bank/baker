package webshop;

import java.util.List;

public class ReserveItems implements JWebshopRecipe.ReserveItems {

    @Override
    public ReserveItemsOutcome apply(String id, List<String> items) {
        return new JWebshopRecipe.ReserveItems.ItemsReserved(items);
    }
}
