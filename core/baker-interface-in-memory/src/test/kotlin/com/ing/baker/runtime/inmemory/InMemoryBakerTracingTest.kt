package com.ing.baker.runtime.inmemory

import com.google.common.collect.ImmutableList
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.inmemory.recipe.CustomerInfo
import com.ing.baker.runtime.inmemory.recipe.LogRecipeFailedImpl
import com.ing.baker.runtime.inmemory.recipe.ManufactureGoods
import com.ing.baker.runtime.inmemory.recipe.SendInvoice
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.CustomerInfoReceived
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.OrderPlaced
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.PaymentMade
import com.ing.baker.runtime.inmemory.recipe.ShipGoods
import com.ing.baker.runtime.inmemory.recipe.ValidateOrder
import com.ing.baker.runtime.inmemory.recipe.WebShopRecipe
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.model.BakerConfig
import io.opentelemetry.api.common.AttributeKey
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.mockito.ArgumentMatchers.anyString
import org.mockito.Mock
import org.mockito.Mockito
import org.mockito.Mockito.`when`
import org.mockito.MockitoAnnotations
import java.time.Duration
import java.util.UUID

class InMemoryBakerTracingTest {

    @Mock
    lateinit var manufactureGoods: ManufactureGoods

    @Mock
    lateinit var sendInvoice: SendInvoice

    @Mock
    lateinit var shipGoods: ShipGoods

    @Mock
    lateinit var validateOrder: ValidateOrder

    @OptIn(ExperimentalDsl::class)
    val recipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe)

    @BeforeEach
    fun setUp() {
        MockitoAnnotations.openMocks(this)
    }

    @Test
    fun `creates lifecycle and interaction spans for happy flow`() {
        TracerFixture.use { fixture ->
            val baker = InMemoryBaker.java(BakerConfig.default(), setupMockImplementations(), fixture.tracer)
            baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

            val goods = "goods"
            val order = "order"
            val trackingId = "trackingId"
            val customerInfo = CustomerInfo("name", "address", "email")

            Mockito.doReturn(ValidateOrder.OrderValid()).`when`(validateOrder).apply(anyString(), anyString())
            Mockito.doReturn(ManufactureGoods.GoodsManufactured(goods)).`when`(manufactureGoods).apply(anyString())
            Mockito.doReturn(SendInvoice.InvoiceSent()).`when`(sendInvoice).apply(customerInfo)
            Mockito.doReturn(ShipGoods.GoodsShipped(trackingId)).`when`(shipGoods).apply(goods, customerInfo)

            val recipeInstanceId = UUID.randomUUID().toString()
            baker.bake(recipe.recipeId(), recipeInstanceId).get()
            baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(OrderPlaced(order))).get()
            baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(CustomerInfoReceived(customerInfo))).get()
            baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(PaymentMade())).get()
            baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(5)).join()

            val spans = fixture.exporter.finishedSpanItems
            val names = spans.map { it.name }

            assertTrue(names.contains("baker.build"))
            assertTrue(names.contains("baker.recipe-instance.created"))
            assertTrue(names.contains("baker.event.received"))
            assertTrue(names.contains("baker.event.fired"))
            assertTrue(names.contains("baker.interaction.ValidateOrder"))
            assertTrue(names.contains("baker.interaction.ShipGoods"))
            assertTrue(names.contains("baker.interaction.SendInvoice"))
            assertTrue(names.any { it.startsWith("baker.interaction.") })

            assertTrue(
                spans.any {
                    it.name == "baker.interaction.ValidateOrder" &&
                        it.status.statusCode == StatusCode.OK &&
                        it.attributes.get(AttributeKey.stringKey("baker.recipe.instance.id")) == recipeInstanceId
                },
                "Expected traced ValidateOrder span with recipe instance attribute"
            )

            val eventSpanIds = spans
                .filter {
                    (it.name == "baker.event.received" || it.name == "baker.event.fired") &&
                        it.attributes.get(AttributeKey.stringKey("baker.recipe.instance.id")) == recipeInstanceId
                }
                .map { it.spanContext.spanId }
                .toSet()

            val validateOrderSpan = spans.firstOrNull {
                it.name == "baker.interaction.ValidateOrder" &&
                    it.attributes.get(AttributeKey.stringKey("baker.recipe.instance.id")) == recipeInstanceId
            }

            assertTrue(
                validateOrderSpan != null && eventSpanIds.contains(validateOrderSpan.parentSpanContext.spanId),
                "Expected interaction span to be linked as child of an event span"
            )
        }
    }

    @Test
    fun `records failed interaction as error span`() {
        TracerFixture.use { fixture ->
            val baker = InMemoryBaker.java(BakerConfig.default(), setupMockImplementations(), fixture.tracer)
            baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

            val goods = "goods"
            val order = "order"
            val customerInfo = CustomerInfo("name", "address", "email")

            `when`(validateOrder.apply(anyString(), anyString())).thenReturn(ValidateOrder.OrderValid())
            `when`(manufactureGoods.apply(anyString())).thenReturn(ManufactureGoods.GoodsManufactured(goods))
            `when`(shipGoods.apply(goods, customerInfo)).thenReturn(ShipGoods.GoodsShipped("tracking-id"))
            `when`(sendInvoice.apply(customerInfo)).thenThrow(RuntimeException("Expected tracing failure"))

            val recipeInstanceId = UUID.randomUUID().toString()
            baker.bake(recipe.recipeId(), recipeInstanceId).get()
            baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(OrderPlaced(order))).get()
            baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(CustomerInfoReceived(customerInfo))).get()
            baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(PaymentMade())).get()
            baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(5)).join()

            val spans = fixture.exporter.finishedSpanItems

            assertTrue(
                spans.any {
                    it.name == "baker.interaction.SendInvoice" &&
                        it.status.statusCode == StatusCode.ERROR &&
                        it.attributes.get(AttributeKey.stringKey("error.type")) == "interaction.failure"
                },
                "Expected failed SendInvoice interaction to be traced as an error span"
            )
        }
    }

    private fun setupMockImplementations(): List<Any> {
        return ImmutableList.of(manufactureGoods, sendInvoice, shipGoods, validateOrder, LogRecipeFailedImpl())
    }

    private class TracerFixture private constructor(
        val exporter: InMemorySpanExporter,
        val tracerProvider: SdkTracerProvider,
        val tracer: Tracer
    ) : AutoCloseable {

        override fun close() {
            tracerProvider.close()
            exporter.reset()
        }

        companion object {
            inline fun use(block: (TracerFixture) -> Unit) {
                val exporter = InMemorySpanExporter.create()
                val tracerProvider = SdkTracerProvider.builder()
                    .addSpanProcessor(SimpleSpanProcessor.create(exporter))
                    .build()
                val openTelemetry = OpenTelemetrySdk.builder()
                    .setTracerProvider(tracerProvider)
                    .build()

                TracerFixture(
                    exporter = exporter,
                    tracerProvider = tracerProvider,
                    tracer = openTelemetry.getTracer("test.inmemory.baker")
                ).use(block)
            }
        }
    }
}

