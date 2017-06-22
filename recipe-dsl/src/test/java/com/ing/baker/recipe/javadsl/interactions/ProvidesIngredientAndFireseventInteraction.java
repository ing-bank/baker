package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.ProvidesIngredient;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.events.InteractionProvidedEvent;

public interface ProvidesIngredientAndFireseventInteraction extends Interaction {
    @ProvidesIngredient("firstProvidedIngredient")
    @FiresEvent(oneOf = InteractionProvidedEvent.class)
    String apply(@RequiresIngredient("initialIngredient") String initialIngredient);
}

