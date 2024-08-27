package examples.kotlin.application

import com.ing.baker.runtime.kotlindsl.Baker

class InquiryExample(private val baker: Baker) {

    suspend fun example(recipeInstanceId: String) {
        val ingredient = baker.getIngredient(recipeInstanceId, "orderId")

        val ingredients = baker.getIngredients(recipeInstanceId)

        val events = baker.getEvents(recipeInstanceId)

        val eventNames = baker.getEventNames(recipeInstanceId)

        val recipeInstanceState = baker.getRecipeInstanceState(recipeInstanceId)
    }
}