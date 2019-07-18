package webshop;

import java.util.List;

public class ReserveItemsInstance implements JWebshopRecipe.ReserveItems {

    @Override
    public ReserveItemsOutcome apply(String id, List<String> items) {
        return new ItemsReserved(items);
    }
}
