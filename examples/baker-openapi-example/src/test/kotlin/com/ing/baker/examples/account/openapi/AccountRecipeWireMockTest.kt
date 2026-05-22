package com.ing.baker.examples.account.openapi

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.kotlin.registerKotlinModule
import com.github.tomakehurst.wiremock.WireMockServer
import com.github.tomakehurst.wiremock.client.WireMock.aResponse
import com.github.tomakehurst.wiremock.client.WireMock.post
import com.github.tomakehurst.wiremock.client.WireMock.postRequestedFor
import com.github.tomakehurst.wiremock.client.WireMock.urlEqualTo
import com.github.tomakehurst.wiremock.core.WireMockConfiguration.wireMockConfig
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.examples.account.openapi.generated.api.CreateAccount
import com.ing.baker.examples.account.openapi.generated.endpoint.CreateAccount as CreateAccountEndpoint
import com.ing.baker.openapi.wirespec.Transportation
import com.ing.baker.openapi.wirespec.javaHttpTransportation
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import community.flock.wirespec.integration.jackson.kotlin.WirespecSerialization
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

    private fun createAccountHandler(): CreateAccountEndpoint.Handler {
        val edge = CreateAccountEndpoint.Handler.client(serialization)
        return object : CreateAccountEndpoint.Handler {
            override suspend fun createAccount(
                request: CreateAccountEndpoint.Request
            ): CreateAccountEndpoint.Response<*> = edge.from(transport(edge.to(request)))
        }
    }

    @Test
    fun `recipe fires AccountCreated on 201`() = runBlocking {
        server.stubFor(
            post(urlEqualTo("/accounts")).willReturn(
                aResponse().withStatus(201).withHeader("Content-Type", "application/json")
                    .withBody(objectMapper.writeValueAsString(mapOf(
                        "accountId" to "a1", "userId" to "u1", "profileId" to "p1",
                        "iban" to "NL00", "accountType" to "CURRENT", "currency" to "EUR",
                    )))
            )
        )

        val baker = InMemoryBaker.kotlin(
            implementations = AccountRecipe.apiRecipe.toInteractionInstances(
                handlers = mapOf(CreateAccount to createAccountHandler()),
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
            EventInstance.from(CreateAccountCommand("u1", "p1", "CURRENT", "EUR")),
        )
        baker.awaitCompleted(rid, timeout = 10.seconds)

        val events = baker.getRecipeInstanceState(rid).events.map { it.name }
        assertTrue(events.contains("AccountCreated"), "events were: $events")
        server.verify(postRequestedFor(urlEqualTo("/accounts")))
    }
}
