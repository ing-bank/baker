package examples.kotlin.recipes

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import org.junit.Test

@ExperimentalDsl
class WebShopRecipeTest {
    @Test
    fun `recipe should compile without validation errors`() {
        val validationErrors = RecipeCompiler.compileRecipe(WebShopRecipe.recipe).validationErrors
        assert(validationErrors.isEmpty()) {
            "Recipe compilation resulted in validation errors: \n${validationErrors.joinToString(separator = "\n")}"
        }
    }
}