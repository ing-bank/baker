package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.events.InteractionEventExample;
import com.ing.baker.recipe.javadsl.events.InteractionProvidedEvent;
import com.ing.baker.recipe.javadsl.events.InteractionProvidedEvent2;

public interface FiresTwoEventInteraction {
    @FiresEvent(oneOf = {InteractionProvidedEvent.class, InteractionProvidedEvent2.class})
    InteractionEventExample apply(@RequiresIngredient("initialIngredient") String initialIngredient);
}

