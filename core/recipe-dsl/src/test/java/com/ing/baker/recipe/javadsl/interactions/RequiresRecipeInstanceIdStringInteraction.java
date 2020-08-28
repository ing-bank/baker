package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.RecipeInstanceId;
import com.ing.baker.recipe.annotations.RequiresIngredient;

public interface RequiresRecipeInstanceIdStringInteraction {
    String apply(@RecipeInstanceId String recipeInstanceId, @RequiresIngredient("initialIngredient") String initialIngredient);
}
