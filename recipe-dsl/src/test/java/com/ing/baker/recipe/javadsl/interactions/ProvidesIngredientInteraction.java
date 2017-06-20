package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.ProvidesIngredient;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

public interface ProvidesIngredientInteraction extends Interaction {
    @ProvidesIngredient("firstProvidedIngredient")
    String apply(@RequiresIngredient("initialIngredient") String initialIngredient);
}
