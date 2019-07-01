import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.recipe.javadsl.Recipe;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

public class RecipeCompilerTests {

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    static class EventA {}
    static class EventB {}
    static class EventC {}
    static class EventD {}
    static class EventE {}

    @Test
    public void shouldBeFixedForGithubIssue216() {
        // Note, all comments are stated as if the bug still existed
        // "Duplicated" EventA will not be added
        // Because Set backing sensoryEvents has <=4 elements (is a specialized Set.Set4) and only uses `equals` in `contains`
        Recipe recipe1 = new Recipe("recipe1")
                .withSensoryEvents(EventA.class, EventB.class, EventC.class, EventD.class)
                .withSensoryEventsNoFiringLimit(EventA.class);

        // "Duplicated" EventA will be added
        // Because Set backing sensoryEvents has >4 elements (is a HashSet) and uses `hashcode` in `contains`
        Recipe recipe2 = new Recipe("recipe2")
                .withSensoryEvents(EventA.class, EventB.class, EventC.class, EventD.class, EventE.class)
                .withSensoryEventsNoFiringLimit(EventA.class);

        // So compilation of Recipe1 succeeds because there are no "duplicates"
        RecipeCompiler.compileRecipe(recipe1);

        // But compilation of Recipe2 will fail
        RecipeCompiler.compileRecipe(recipe2);
    }
}
