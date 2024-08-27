package examples.scala.application

import com.ing.baker.runtime.scaladsl.Baker

class InquiryExample(val baker: Baker) {

  def example(recipeInstanceId: String): Unit = {
    val ingredient = baker.getIngredient(recipeInstanceId, "orderId")

    val ingredients = baker.getIngredients(recipeInstanceId)

    val events = baker.getEvents(recipeInstanceId)

    val eventNames = baker.getEventNames(recipeInstanceId)

    val recipeInstanceState = baker.getRecipeInstanceState(recipeInstanceId)
  }
}
