package examples.kotlin.application

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import examples.kotlin.events.OrderPlaced
import examples.kotlin.ingredients.Address
import examples.kotlin.interactions.CancelOrderImpl
import examples.kotlin.interactions.CheckStockImpl
import examples.kotlin.interactions.ShipOrderImpl
import examples.kotlin.recipes.WebShopRecipe
import kotlinx.coroutines.runBlocking
import java.util.*

@ExperimentalDsl
fun main(): Unit = runBlocking {
    val baker = InMemoryBaker.kotlin(
        implementations = listOf(CheckStockImpl, CancelOrderImpl, ShipOrderImpl)
    )

    val recipeId = baker.addRecipe(
        compiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe),
        validate = true
    )

    val recipeInstanceId = UUID.randomUUID().toString()
    val sensoryEvent = EventInstance.from(orderPlaced)

    baker.bake(recipeId, recipeInstanceId)
    baker.fireEventAndResolveWhenCompleted(recipeInstanceId, sensoryEvent)
}

private val orderPlaced = OrderPlaced(
    orderId = "123",
    customerId = "456",
    productIds = listOf("iPhone", "PlayStation5"),
    address = Address(
        street = "Hoofdstraat",
        city = "Amsterdam",
        zipCode = "1234AA",
        country = "The Netherlands"
    )
)
