package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;

public interface InteractionWithNameField {

    String name = "NameField";

    class InteractionWithNameFieldEvent { }

    @FiresEvent(oneOf = { InteractionWithNameFieldEvent.class })
    InteractionWithNameFieldEvent apply();
}