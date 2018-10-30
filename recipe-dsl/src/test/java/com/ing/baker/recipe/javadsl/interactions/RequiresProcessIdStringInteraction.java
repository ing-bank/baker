package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.ProcessId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

public interface RequiresProcessIdStringInteraction extends Interaction {
    String apply(@ProcessId String processId, @RequiresIngredient("initialIngredient") String initialIngredient);
}
