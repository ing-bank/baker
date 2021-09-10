package com.ing.baker.test.javadsl.recipe;

import java.util.List;
import java.util.concurrent.CompletableFuture;


public class ReserveItemsImpl implements ReserveItems {
    @Override
    public CompletableFuture<ReserveItemsOutput> apply(String orderId, List<String> items) {
        return CompletableFuture.completedFuture(new ItemsReserved());
    }
}
