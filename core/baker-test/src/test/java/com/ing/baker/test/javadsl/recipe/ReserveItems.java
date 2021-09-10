package com.ing.baker.test.javadsl.recipe;

import com.ing.baker.recipe.annotations.AsyncInteraction;
import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

import java.util.List;
import java.util.concurrent.CompletableFuture;

public interface ReserveItems extends Interaction {
    @AsyncInteraction
    @FiresEvent(oneOf = {ItemsReserved.class, OrderHadUnavailableItems.class})
    CompletableFuture<ReserveItemsOutput> apply(
            @RequiresIngredient("orderId") String orderId,
            @RequiresIngredient("items") List<String> items);

    interface ReserveItemsOutput {}
    class ItemsReserved implements ReserveItemsOutput {}
    class OrderHadUnavailableItems implements ReserveItemsOutput {}
}
