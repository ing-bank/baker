package examples.kotlin.application

import com.ing.baker.runtime.kotlindsl.Baker

suspend fun retryExample(baker: Baker, recipeInstanceId: String) {
    baker.retryInteraction(recipeInstanceId, "ShipOrder")
}