package com.ing.baker.test.javadsl.recipe;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.test.EventsFlow;

public class WebshopRecipe {
    public static final Recipe RECIPE = new Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced.class)
            .withInteraction(InteractionDescriptor.of(ReserveItems.class));

    public static final EventsFlow HAPPY_FLOW = EventsFlow.ofClasses(OrderPlaced.class, ReserveItems.ItemsReserved.class);
}
