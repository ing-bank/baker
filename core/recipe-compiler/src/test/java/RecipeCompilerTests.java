import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.il.petrinet.InteractionTransition;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.recipe.javadsl.ResultEvent;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.stream.Collectors;

public class RecipeCompilerTests {

    static class EventA {
    }

    static class EventB {
    }

    static class EventC {
    }

    static class EventD {
    }

    static class EventE {
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

    @Test
    public void shouldAddInteractionsForResultEvents() {

        Recipe recipe = new Recipe("recipe1")
                .withSensoryEvents(EventB.class, EventC.class, EventD.class)
                .withSensoryEventsNoFiringLimit(EventA.class)
                .withResultEvent(new ResultEvent("Success")
                        .withRequiredEvents(EventB.class, EventC.class));


        CompiledRecipe compiled = RecipeCompiler.compileRecipe(recipe);

        Object actual = convertList(compiled.petriNet().transitions())
                .stream()
                .filter(InteractionTransition.class::isInstance)
                .map(i -> ((InteractionTransition) i).interactionName())
                .collect(Collectors.toUnmodifiableList());

        Assertions.assertEquals(java.util.List.of("$ResultEventInteraction$Success"), actual);

    }

    private java.util.List convertList(scala.collection.immutable.Set list) {
        java.util.List l = new ArrayList();
        list.foreach(i -> l.add(i));
        return l;
    }
}
