package examples.kotlin.application

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.Baker
import examples.kotlin.events.OrderPlaced
import kotlin.time.Duration.Companion.seconds

class FireEventAndResolveOnEvent(private val baker: Baker) {

    suspend fun example(recipeInstanceId: String, orderPlaced: OrderPlaced) {
        val orderPlacedEvent = EventInstance.from(orderPlaced)
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, orderPlacedEvent)
        baker.awaitEvent(recipeInstanceId, "ExpectedEvent", 5.seconds)
    }
}