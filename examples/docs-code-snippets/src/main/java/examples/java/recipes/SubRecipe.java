package examples.java.recipes;

import com.ing.baker.recipe.javadsl.Recipe;

public class SubRecipe {

    public final static Recipe recipe = new Recipe("root recipe")
            .withSubRecipe(new Recipe("sub recipe 1"))
            .withSubRecipe(new Recipe("sub recipe 2")
                    .withSubRecipe(new Recipe("sub sub recipe 2.1"))
            );

}
