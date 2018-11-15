package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.events.InteractionProvidedEvent;

public interface FiresEventInteraction {
    @FiresEvent(oneOf = InteractionProvidedEvent.class)
    InteractionProvidedEvent apply(@RequiresIngredient("initialIngredient") String initialIngredient);
}

