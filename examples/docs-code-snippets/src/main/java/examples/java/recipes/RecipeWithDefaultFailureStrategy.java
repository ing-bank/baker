package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;

public class RecipeWithDefaultFailureStrategy {

    public final static Recipe recipe = new Recipe("example")
        .withDefaultFailureStrategy(
            InteractionFailureStrategy.FireEvent("recipeFailed")
        );
}
