package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;

public class RecipeBlockInteraction {

    public final static Recipe recipe = new Recipe("example")
        .withDefaultFailureStrategy(
            InteractionFailureStrategy.BlockInteraction()
        );
}
