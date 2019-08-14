package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.ProcessId;
import com.ing.baker.recipe.annotations.RequiresIngredient;

public interface RequiresProcessIdStringInteraction {
    String apply(@ProcessId String processId, @RequiresIngredient("initialIngredient") String initialIngredient);
}
