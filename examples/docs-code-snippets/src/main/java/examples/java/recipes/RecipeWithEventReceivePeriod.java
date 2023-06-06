package examples.java.recipes;

import com.ing.baker.recipe.javadsl.Recipe;

import java.time.Duration;

public class RecipeWithEventReceivePeriod {

    public final static Recipe recipe = new Recipe("example")
        .withEventReceivePeriod(Duration.ofHours(5));
}
