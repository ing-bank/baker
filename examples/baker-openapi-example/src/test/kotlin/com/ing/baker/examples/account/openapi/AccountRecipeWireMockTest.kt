package com.ing.baker.examples.account.openapi

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.kotlin.registerKotlinModule
import com.github.tomakehurst.wiremock.WireMockServer
import com.github.tomakehurst.wiremock.client.WireMock.equalTo
import com.github.tomakehurst.wiremock.client.WireMock.matchingJsonPath
import com.github.tomakehurst.wiremock.client.WireMock.postRequestedFor
import com.github.tomakehurst.wiremock.client.WireMock.urlEqualTo
import com.github.tomakehurst.wiremock.core.WireMockConfiguration.wireMockConfig
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.examples.account.openapi.generated.endpoint.CreateAccount as CreateAccountEndpoint
import com.ing.baker.examples.account.openapi.generated.model.AccountDto
import com.ing.baker.openapi.wirespec.Transportation
import com.ing.baker.openapi.wirespec.javaHttpTransportation
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import community.flock.wirespec.integration.jackson.kotlin.WirespecSerialization
import community.flock.wirespec.integration.wiremock.kotlin.wirespec
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.UUID
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

@OptIn(ExperimentalDsl::class)
class AccountRecipeWireMockTest {

    private lateinit var server: WireMockServer
    private lateinit var transport: Transportation
    private val objectMapper = ObjectMapper().registerKotlinModule()
    private val serialization = WirespecSerialization(objectMapper)

    @BeforeEach fun setUp() {
        server = WireMockServer(wireMockConfig().dynamicPort()).also { it.start() }
        transport = javaHttpTransportation("http://localhost:${server.port()}")
    }
    @AfterEach fun tearDown() { server.stop() }

    @Test
    fun `recipe fires AccountCreated on 201`() = runBlocking {
        // wirespec<EndpointType>() drives the WireMock matcher from the endpoint's
        // method + path template; willReturn(...) takes the typed Wirespec.Response
        // directly — no manual JSON body assembly.
        server.stubFor(
            wirespec<CreateAccountEndpoint>().willReturn(
                CreateAccountEndpoint.Response201(
                    AccountDto(
                        accountId = "a1",
                        userId = "u1",
                        profileId = "p1",
                        iban = "NL00",
                        accountType = "CURRENT",
                        currency = "EUR",
                    )
                ),
                serialization,
            )
        )

        val baker = InMemoryBaker.kotlin(
            implementations = AccountRecipe.apiRecipe.toInteractionInstances(
                transport = transport,
                serialization = serialization,
            ),
        )
        val recipeId = baker.addRecipe(
            compiledRecipe = RecipeCompiler.compileRecipe(AccountRecipe.apiRecipe.recipe),
            validate = true,
        )
        val rid = UUID.randomUUID().toString()
        baker.bake(recipeId, rid)
        baker.fireSensoryEventAndAwaitReceived(
            rid,
            EventInstance.from(
                CreateAccountCommand(
                    customerId = "u1",
                    profileId = "p1",
                    accountType = "CURRENT",
                    currency = "EUR",
                )
            ),
        )
        baker.awaitCompleted(rid, timeout = 10.seconds)

        val events = baker.getRecipeInstanceState(rid).events.map { it.name }
        assertTrue(events.contains("AccountCreated"), "events were: $events")
        // The customerId ingredient was renamed to userId for the API call —
        // proves the inputFrom mapper wired the value through.
        server.verify(
            postRequestedFor(urlEqualTo("/accounts"))
                .withRequestBody(matchingJsonPath("$.userId", equalTo("u1")))
        )
    }
}
