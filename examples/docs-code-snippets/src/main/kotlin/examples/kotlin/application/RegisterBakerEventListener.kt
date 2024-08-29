package examples.kotlin.application

import com.ing.baker.runtime.kotlindsl.Baker

class RegisterBakerEventListener(private val baker: Baker) {

    suspend fun example() {
        baker.registerBakerEventListener { bakerEvent ->
            println("Received event: $bakerEvent")
        }
    }
}