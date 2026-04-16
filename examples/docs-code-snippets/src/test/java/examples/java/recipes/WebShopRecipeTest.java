package examples.java.recipes;

import com.ing.baker.compiler.RecipeCompiler;
import org.junit.Test;

import static org.junit.Assert.assertTrue;

public class WebShopRecipeTest {

    @Test
    public void recipeShouldCompileWithoutValidationErrors() {
        var validationErrors = RecipeCompiler.compileRecipe(WebShopRecipe.recipe).getValidationErrors();
        assertTrue(
            String.format("Recipe compilation resulted in validation errors: \n%s", validationErrors),
            validationErrors.isEmpty()
        );
    }
}