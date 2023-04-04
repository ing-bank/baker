package com.ing.baker.recipe.kotlindsl;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

import java.util.List;

public interface JavaInteraction extends Interaction {

    interface ReserveItemsOutcome {
    }

    class OrderHadUnavailableItems implements ReserveItemsOutcome {

        public final List<String> unavailableItems;

        public OrderHadUnavailableItems(List<String> unavailableItems) {
            this.unavailableItems = unavailableItems;
        }
    }

    class ItemsReserved implements ReserveItemsOutcome {

        public final List<String> reservedItems;

        public ItemsReserved(List<String> reservedItems) {
            this.reservedItems = reservedItems;
        }
    }

    @FiresEvent(oneOf = { ItemsReserved.class, OrderHadUnavailableItems.class })
    ReserveItemsOutcome apply(
            @RequiresIngredient("orderId") String id,
            @RequiresIngredient("items") List<String> items
    );
}
