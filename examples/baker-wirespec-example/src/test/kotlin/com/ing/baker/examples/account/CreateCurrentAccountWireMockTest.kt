package com.ing.baker.examples.account

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.kotlin.registerKotlinModule
import com.github.tomakehurst.wiremock.WireMockServer
import com.github.tomakehurst.wiremock.client.WireMock.*
import com.github.tomakehurst.wiremock.core.WireMockConfiguration.wireMockConfig
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.examples.account.generated.*
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import community.flock.wirespec.integration.jackson.kotlin.WirespecSerialization
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

@ExperimentalDsl
class CreateCurrentAccountWireMockTest {

    private lateinit var wireMockServer: WireMockServer
    private lateinit var transport: Transportation

    private val objectMapper = ObjectMapper().registerKotlinModule()
    private val serialization = WirespecSerialization(objectMapper)

    @BeforeEach
    fun setUp() {
        wireMockServer = WireMockServer(wireMockConfig().dynamicPort())
        wireMockServer.start()
        transport = javaHttpTransportation("http://localhost:${wireMockServer.port()}")
    }

    @AfterEach
    fun tearDown() {
        wireMockServer.stop()
    }

    @Test
    fun `should orchestrate full current account creation via HTTP`() = runBlocking {
        // Stub POST /users
        wireMockServer.stubFor(
            post(urlEqualTo("/users"))
                .willReturn(
                    aResponse()
                        .withStatus(201)
                        .withHeader("Content-Type", "application/json")
                        .withBody(
                            objectMapper.writeValueAsString(
                                mapOf(
                                    "id" to "user-1",
                                    "firstName" to "John",
                                    "lastName" to "Doe",
                                    "email" to "john.doe@example.com",
                                    "dateOfBirth" to "1990-01-01"
                                )
                            )
                        )
                )
        )

        // Stub POST /profiles
        wireMockServer.stubFor(
            post(urlEqualTo("/profiles"))
                .willReturn(
                    aResponse()
                        .withStatus(201)
                        .withHeader("Content-Type", "application/json")
                        .withBody(
                            objectMapper.writeValueAsString(
                                mapOf(
                                    "profileId" to "profile-1",
                                    "userId" to "user-1",
                                    "address" to "123 Main Street, Amsterdam",
                                    "phoneNumber" to "+31612345678"
                                )
                            )
                        )
                )
        )

        // Stub POST /accounts
        wireMockServer.stubFor(
            post(urlEqualTo("/accounts"))
                .willReturn(
                    aResponse()
                        .withStatus(201)
                        .withHeader("Content-Type", "application/json")
                        .withBody(
                            objectMapper.writeValueAsString(
                                mapOf(
                                    "accountId" to "account-1",
                                    "userId" to "user-1",
                                    "profileId" to "profile-1",
                                    "iban" to "NL00INGB0001234567",
                                    "accountType" to "CURRENT",
                                    "currency" to "EUR"
                                )
                            )
                        )
                )
        )

        val baker = InMemoryBaker.kotlin(
            implementations = listOf(
                CreateUserInteractionImpl(createUserHandler(transport, serialization)),
                CreateProfileInteractionImpl(createProfileHandler(transport, serialization)),
                CreateAccountInteractionImpl(createAccountHandler(transport, serialization))
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
        assertTrue(eventNames.contains("Finish"), "Should have fired Finish event after all APIs succeeded")

        // Verify HTTP requests were made
        wireMockServer.verify(postRequestedFor(urlEqualTo("/users")))
        wireMockServer.verify(postRequestedFor(urlEqualTo("/profiles")))
        wireMockServer.verify(postRequestedFor(urlEqualTo("/accounts")))
    }
}
