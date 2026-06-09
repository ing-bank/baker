package com.ing.baker.runtime.javadsl;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;

interface AnnotatedParentInteraction {
    @FiresEvent(oneOf = {SimpleEvent.class})
    public SimpleEvent apply(@RequiresIngredient("renamedInput") String input);
}
