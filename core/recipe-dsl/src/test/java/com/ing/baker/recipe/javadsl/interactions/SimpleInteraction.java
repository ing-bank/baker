package com.ing.baker.recipe.javadsl.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;

public interface SimpleInteraction {

    class InitialIngredientEvent {
        final String initialIngredient;
        public InitialIngredientEvent(String initialIngredient) {
            this.initialIngredient = initialIngredient;
        }
    }

    @FiresEvent(oneOf = { InitialIngredientEvent.class })
    InitialIngredientEvent apply(@RequiresIngredient("initialIngredient") String initialIngredient);
}
