package webshop.simple;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import webshop.simple.ingredients.Item;
import webshop.simple.ingredients.ReservedItems;

import java.util.List;

public interface ReserveItems extends Interaction {

    interface ReserveItemsOutcome {
    }

    class OrderHadUnavailableItems implements ReserveItemsOutcome {

        public final List<Item> unavailableItems;

        public OrderHadUnavailableItems(List<Item> unavailableItems) {
            this.unavailableItems = unavailableItems;
        }
    }

    class ItemsReserved implements ReserveItemsOutcome {

        public final ReservedItems reservedItems;

        public ItemsReserved(ReservedItems reservedItems) {
            this.reservedItems = reservedItems;
        }
    }

    @FiresEvent(oneOf = {OrderHadUnavailableItems.class, ItemsReserved.class})
    ReserveItemsOutcome apply(@RequiresIngredient("items") List<Item> items);
}
