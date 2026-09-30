package com.ing.baker.examples.account

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import com.ing.baker.examples.account.generated.*
import com.ing.baker.examples.account.generated.endpoint.CreateUser
import com.ing.baker.examples.account.generated.endpoint.CreateProfile
import com.ing.baker.examples.account.generated.endpoint.CreateAccount
import com.ing.baker.examples.account.generated.model.*
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Test
import java.util.*
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

@ExperimentalDsl
class CreateCurrentAccountTest {

    private val userHandler = object : CreateUser.Handler {
        override suspend fun createUser(request: CreateUser.Request): CreateUser.Response<*> {
            return CreateUser.Response201(
                body = UserDto(
                    id = "user-1",
                    firstName = request.body.firstName,
                    lastName = request.body.lastName,
                    email = request.body.email,
                    dateOfBirth = request.body.dateOfBirth
                )
            )
        }
    }

    private val profileHandler = object : CreateProfile.Handler {
        override suspend fun createProfile(request: CreateProfile.Request): CreateProfile.Response<*> {
            return CreateProfile.Response201(
                body = ProfileDto(
                    profileId = "profile-1",
                    userId = request.body.userId,
                    address = request.body.address,
                    phoneNumber = request.body.phoneNumber
                )
            )
        }
    }

    private val accountHandler = object : CreateAccount.Handler {
        override suspend fun createAccount(request: CreateAccount.Request): CreateAccount.Response<*> {
            return CreateAccount.Response201(
                body = AccountDto(
                    accountId = "account-1",
                    userId = request.body.userId,
                    profileId = request.body.profileId,
                    iban = "NL00INGB0001234567",
                    accountType = request.body.accountType,
                    currency = request.body.currency
                )
            )
        }
    }

    @Test
    fun `should orchestrate full current account creation`() = runBlocking {
        val baker = InMemoryBaker.kotlin(
            implementations = listOf(
                CreateUserInteractionImpl(userHandler),
                CreateProfileInteractionImpl(profileHandler),
                CreateAccountInteractionImpl(accountHandler)
            )
        )

        val recipeId = baker.addRecipe(
            compiledRecipe = RecipeCompiler.compileRecipe(CreateCurrentAccountRecipe.recipe),
            validate = true
        )

        val recipeInstanceId = UUID.randomUUID().toString()
        baker.bake(recipeId, recipeInstanceId)

        val sensoryEvent = EventInstance.from(
            CreateCurrentAccountEvent(
                firstName = "John",
                lastName = "Doe",
                email = "john.doe@example.com",
                dateOfBirth = "1990-01-01",
                address = "123 Main Street, Amsterdam",
                phoneNumber = "+31612345678",
                accountType = "CURRENT",
                currency = "EUR"
            )
        )

        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, sensoryEvent)
        baker.awaitCompleted(recipeInstanceId, timeout = 10.seconds)

        val state = baker.getRecipeInstanceState(recipeInstanceId)
        val eventNames = state.events.map { it.name }

        assertTrue(eventNames.contains("CreateCurrentAccountEvent"), "Should have received sensory event")
        assertTrue(eventNames.contains("CreateUserResponse201"), "Should have created user")
        assertTrue(eventNames.contains("CreateProfileResponse201"), "Should have created profile")
        assertTrue(eventNames.contains("CreateAccountResponse201"), "Should have created account")
    }
}
