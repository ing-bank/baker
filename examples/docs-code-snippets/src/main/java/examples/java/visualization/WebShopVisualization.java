package examples.java.visualization;

import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import examples.java.recipes.WebShopRecipe;

public class WebShopVisualization {
    public void printVisualizationString() {
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe);
        String graphvizString = compiledRecipe.getRecipeVisualization();
        System.out.println(graphvizString);
    }
}
