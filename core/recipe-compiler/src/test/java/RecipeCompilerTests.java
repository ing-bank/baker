import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.recipe.javadsl.Recipe;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class RecipeCompilerTests {

    static class EventA {}
    static class EventB {}
    static class EventC {}
    static class EventD {}
    static class EventE {}

    @Test
    public void shouldCompileSimpleRecipe(){
        Recipe recipe = new Recipe("recipe")
                .withSensoryEvents(EventA.class);
        CompiledRecipe compiled = RecipeCompiler.compileRecipe(recipe);

        Assertions.assertEquals("bb928e13daf86557", compiled.recipeId());

    }

    @Test
    public void shouldFailOnDuplicatedEventsEvenWithFiringLimitDifference() {
        // "Duplicated" EventA
        // Because Set backing sensoryEvents has <=4 elements (is a specialized Set.Set4) it only uses `equals` in `contains`
        Recipe recipe1 = new Recipe("recipe1")
                .withSensoryEvents(EventA.class, EventB.class, EventC.class, EventD.class)
                .withSensoryEventsNoFiringLimit(EventA.class);

        // "Duplicated" EventA
        // Because Set backing sensoryEvents has >4 elements (is a HashSet) and uses `hashcode` in `contains`
        Recipe recipe2 = new Recipe("recipe2")
                .withSensoryEvents(EventA.class, EventB.class, EventC.class, EventD.class, EventE.class)
                .withSensoryEventsNoFiringLimit(EventA.class);

        Assertions.assertThrows(IllegalStateException.class, () ->
            RecipeCompiler.compileRecipe(recipe1));

        Assertions.assertThrows(IllegalStateException.class, () ->
            RecipeCompiler.compileRecipe(recipe2));
    }
}
