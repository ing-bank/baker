package examples.kotlin.application

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import examples.kotlin.events.OrderPlaced
import examples.kotlin.interactions.CancelOrderImpl
import examples.kotlin.interactions.CheckStockImpl
import examples.kotlin.interactions.ShipOrderImpl
import examples.kotlin.recipes.WebShopRecipe
import java.util.*

@ExperimentalDsl
suspend fun execute(orderPlaced: OrderPlaced) {
    val implementations = listOf(CheckStockImpl, CancelOrderImpl, ShipOrderImpl)
    val baker = InMemoryBaker.kotlin(implementations)

    // Adds the recipe to the Baker runtime and validates there are interaction instances for each interaction.
    val recipeId = baker.addRecipe(
        compiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe),
        validate = true
    )

    val recipeInstanceId = UUID.randomUUID().toString()

    // Start one instance of the process by baking the recipe.
    baker.bake(recipeId, recipeInstanceId)

    // Fire the OrderPlaced sensory event
    baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.from(orderPlaced))
}

