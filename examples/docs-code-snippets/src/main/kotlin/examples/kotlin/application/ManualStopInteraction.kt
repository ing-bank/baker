package examples.kotlin.application

import com.ing.baker.runtime.kotlindsl.Baker

suspend fun stopExample(baker: Baker, recipeInstanceId: String) {
    baker.stopRetryingInteraction(recipeInstanceId, "ShipOrder")
}