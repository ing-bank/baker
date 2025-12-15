package examples.kotlin.application

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.Baker
import examples.kotlin.events.OrderPlaced
import kotlinx.coroutines.async
import kotlinx.coroutines.coroutineScope
import kotlin.time.Duration.Companion.seconds

class AwaitEventWaitForNext(private val baker: Baker) {

    suspend fun example(recipeInstanceId: String, orderPlaced: OrderPlaced) = coroutineScope {
        val orderPlacedEvent = EventInstance.from(orderPlaced)
        
        // Pattern: Start waiting BEFORE firing the sensory event
        // waitForNext = true checks for *new* occurrences of the event
        // We use async to start the "await" concurrently 
        val awaitDeferred = async { 
            baker.awaitEvent(recipeInstanceId, "ExpectedEvent", timeout = 5.seconds, waitForNext = true) 
        }
        
        // Fire the event
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, orderPlacedEvent)
        
        // Now wait for the event to occur
        awaitDeferred.await()
    }
}
