package examples.kotlin.application

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.Baker

suspend fun resolveExample(baker: Baker, recipeInstanceId: String) {
    baker.resolveInteraction(
        recipeInstanceId,
        "ShipOrder",
        EventInstance.from("ShippingFailed")
    )
}