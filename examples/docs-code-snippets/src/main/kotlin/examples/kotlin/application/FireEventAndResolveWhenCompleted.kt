package examples.kotlin.application

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.Baker
import examples.kotlin.events.OrderPlaced

class FireEventAndResolveWhenCompleted(private val baker: Baker) {

    suspend fun example(recipeInstanceId: String, orderPlaced: OrderPlaced) {
        val orderPlacedEvent = EventInstance.from(orderPlaced)
        val sensoryEventResult = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, orderPlacedEvent)
    }
}