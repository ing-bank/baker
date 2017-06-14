package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.ProcessId;
import com.ing.baker.recipe.annotations.ProvidesIngredient;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

import java.util.UUID;

public interface RequiresProcessIdUUIDInteraction extends Interaction {
    String apply(@ProcessId UUID processId, @RequiresIngredient("initialIngredient") String initialIngredient);
}
