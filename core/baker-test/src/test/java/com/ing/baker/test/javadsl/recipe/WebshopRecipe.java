package com.ing.baker.test.javadsl.recipe;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;

public class WebshopRecipe {
    public static final Recipe TEST_RECIPE = new Recipe("TestRecipe")
            .withSensoryEvent(OrderPlaced.class)
            .withInteraction(InteractionDescriptor.of(ReserveItems.class));
}
