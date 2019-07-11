package webshop;

import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import org.junit.Test;
import scala.Console;

import com.ing.baker.runtime.javadsl.EventInstance;

public class JWebshopRecipeTests {

    public static class OrderPlaced {

        public final String orderId;
        public final String[] items;

        public OrderPlaced(String orderId, String[] items) {
            this.orderId = orderId;
            this.items = items;
        }
    }

    @Test
    public void shouldCompileTheRecipeWithoutIssues() {
        RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);
    }

    @Test
    public void shouldVisualizeTheRecipeWithoutIssues() {

        String[] items = {"item1", "item2"};
        OrderPlaced order1 = new OrderPlaced("uuid-0123456789", items);
        EventInstance order1Event = EventInstance.from(order1);

        CompiledRecipe recipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);
        String visualization = recipe.getRecipeVisualization();
        System.out.println(Console.GREEN() + "Recipe visualization, paste this into webgraphviz.com:");
        System.out.println(visualization + Console.RESET());
    }
}
