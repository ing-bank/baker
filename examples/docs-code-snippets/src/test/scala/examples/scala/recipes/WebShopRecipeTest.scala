package examples.scala.recipes

import com.ing.baker.compiler.RecipeCompiler
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class WebShopRecipeTest extends AnyFlatSpec with Matchers {
  "Recipe" should "compile without validation errors" in {
    val validationErrors = RecipeCompiler.compileRecipe(WebShopRecipe.recipe).validationErrors
    assert(validationErrors.isEmpty)
  }
}
