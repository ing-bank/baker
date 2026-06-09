package com.ing.baker.runtime.javadsl;

import com.ing.baker.recipe.annotations.RequiresIngredient;

public class AnnotatedInteraction3 implements AnnotatedParentInteraction {

    public SimpleEvent apply(@RequiresIngredient("renamedInput2")String input) {
        return new SimpleEvent("output");
    }
}
