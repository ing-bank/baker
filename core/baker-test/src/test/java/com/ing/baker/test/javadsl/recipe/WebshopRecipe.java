package com.ing.baker.test.javadsl.recipe;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.test.javadsl.BakerEventsFlow;

public class WebshopRecipe {
    public static final Recipe RECIPE = new Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced.class)
            .withInteraction(InteractionDescriptor.of(ReserveItems.class));

    public static final BakerEventsFlow HAPPY_FLOW = BakerEventsFlow.ofClass(OrderPlaced.class, ReserveItems.ItemsReserved.class);
}
