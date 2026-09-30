package com.ing.baker.examples.account

import com.github.tomakehurst.wiremock.WireMockServer
import com.github.tomakehurst.wiremock.client.WireMock.postRequestedFor
import com.github.tomakehurst.wiremock.client.WireMock.urlEqualTo
import com.github.tomakehurst.wiremock.core.WireMockConfiguration.wireMockConfig
import com.ing.baker.examples.account.generated.endpoint.CreateAccount
import com.ing.baker.examples.account.generated.endpoint.CreateProfile
import com.ing.baker.examples.account.generated.endpoint.CreateUser
import com.ing.baker.examples.account.generated.model.*
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

@ExperimentalDsl
class ApplicationTest {

    private lateinit var wireMockServer: WireMockServer
    private lateinit var app: Application

    @BeforeEach
    fun setUp() = runBlocking {
        wireMockServer = WireMockServer(wireMockConfig().dynamicPort())
        wireMockServer.start()
        app = Application.of("http://localhost:${wireMockServer.port()}")
    }

    @AfterEach
    fun tearDown() {
        wireMockServer.stop()
    }

    @Test
    fun `should orchestrate full current account creation via HTTP`() = runBlocking {
        wireMockServer.stubFor(CreateUser.Response201(
            body = UserDto(
                id = "user-1",
                firstName = "John",
                lastName = "Doe",
                email = "john.doe@example.com",
                dateOfBirth = "1990-01-01"
            )
        ))

        wireMockServer.stubFor(CreateProfile.Response201(
            body = ProfileDto(
                profileId = "profile-1",
                userId = "user-1",
                address = "123 Main Street, Amsterdam",
                phoneNumber = "+31612345678"
            )
        ))

        wireMockServer.stubFor(CreateAccount.Response201(
            body = AccountDto(
                accountId = "account-1",
                userId = "user-1",
                profileId = "profile-1",
                iban = "NL00INGB0001234567",
                accountType = "CURRENT",
                currency = "EUR"
            )
        ))

        val recipeInstanceId = UUID.randomUUID().toString()
        app.baker.bake(app.recipeId, recipeInstanceId)

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

        app.baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, sensoryEvent)
        app.baker.awaitCompleted(recipeInstanceId, timeout = 10.seconds)

        val state = app.baker.getRecipeInstanceState(recipeInstanceId)
        val eventNames = state.events.map { it.name }

        assertTrue(eventNames.contains("CreateCurrentAccountEvent"), "Should have received sensory event")
        assertTrue(eventNames.contains("CreateUserResponse201"), "Should have created user")
        assertTrue(eventNames.contains("CreateProfileResponse201"), "Should have created profile")
        assertTrue(eventNames.contains("CreateAccountResponse201"), "Should have created account")
        assertTrue(eventNames.contains("Finish"), "Should have fired Finish event after all APIs succeeded")

        // Verify HTTP requests were made
        wireMockServer.verify(postRequestedFor(urlEqualTo("/users")))
        wireMockServer.verify(postRequestedFor(urlEqualTo("/profiles")))
        wireMockServer.verify(postRequestedFor(urlEqualTo("/accounts")))
    }
}
