package examples.kotlin.application

import com.ing.baker.runtime.kotlindsl.Baker

class RegisterEventListener(private val baker: Baker) {

    suspend fun example() {
        baker.registerEventListener { recipeInstanceId, eventInstance ->
            println("Recipe Instance: $recipeInstanceId, processed event: $eventInstance ")
        }
    }
}