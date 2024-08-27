package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;

public class RecipeFireEvent {

    public final static Recipe recipe = new Recipe("example")
        .withDefaultFailureStrategy(
            InteractionFailureStrategy.FireEvent("MyEvent")
        );
}
