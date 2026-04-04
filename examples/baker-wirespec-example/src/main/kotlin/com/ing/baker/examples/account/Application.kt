package com.ing.baker.examples.account

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.examples.account.generated.*
import com.ing.baker.examples.account.generated.endpoint.CreateAccount
import com.ing.baker.examples.account.generated.endpoint.CreateProfile
import com.ing.baker.examples.account.generated.endpoint.CreateUser
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.kotlindsl.Baker
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import kotlin.String

@ExperimentalDsl
class Application(
    val baker: Baker,
    val recipeId: String,
) {
    companion object {
        suspend fun create(baseUrl: String,): Application {
            val transport = jvmTransportation(baseUrl)
            val serialization = defaultSerialization()
            val baker = InMemoryBaker.kotlin(
                implementations = listOf(
                    CreateUserInteractionImpl(handle(CreateUser.Handler, transport, serialization)),
                    CreateProfileInteractionImpl(handle(CreateProfile.Handler, transport, serialization)),
                    CreateAccountInteractionImpl(handle(CreateAccount.Handler, transport, serialization)),
                )
            )
            val recipeId = baker.addRecipe(
                compiledRecipe = RecipeCompiler.compileRecipe(Recipe.recipe),
                validate = true,
            )
            return Application(baker, recipeId)
        }

        suspend fun of(baseUrl: String): Application {

            return create(baseUrl)
        }
    }
}
