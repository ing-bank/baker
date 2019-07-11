package webshop;

import com.ing.baker.compiler.RecipeCompiler;
import org.junit.Test;
import scala.Console;

public class JWebshopRecipeTests {

    @Test
    public void shouldCompileTheRecipeWithoutIssues() {
        RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);
    }

    @Test
    public void shouldVisualizeTheRecipeWithoutIssues() {
        String viz = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe).getRecipeVisualization();
        System.out.println(Console.GREEN() + "Recipe visualization, paste this into webgraphviz.com:");
        System.out.println(viz + Console.RESET());
    }
}
