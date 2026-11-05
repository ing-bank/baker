package com.ing.baker.runtime.inmemory

import com.google.common.collect.ImmutableList
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.inmemory.recipe.CustomerInfo
import com.ing.baker.runtime.inmemory.recipe.LogRecipeFailedImpl
import com.ing.baker.runtime.inmemory.recipe.ManufactureGoodsImpl
import com.ing.baker.runtime.inmemory.recipe.SendInvoiceImpl
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.CustomerInfoReceived
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.OrderPlaced
import com.ing.baker.runtime.inmemory.recipe.SensoryEvents.PaymentMade
import com.ing.baker.runtime.inmemory.recipe.ShipGoodsImpl
import com.ing.baker.runtime.inmemory.recipe.ValidateOrder
import com.ing.baker.runtime.inmemory.recipe.WebShopRecipe
import com.ing.baker.runtime.javadsl.Baker
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.model.BakerConfig
import io.opentelemetry.api.common.AttributeKey
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.slf4j.MDC
import java.time.Duration
import java.util.UUID
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit

/**
 * Verifies that the ambient tracing context observed inside an interaction belongs to that very interaction,
 * also when many recipe instances execute concurrently on the shared interaction thread pool.
 */
class InMemoryBakerTracingConcurrencyTest {

    private val instanceCount = 32
    private val concurrencyLevel = 8
    private val invalidTraceId = "00000000000000000000000000000000"

    @OptIn(ExperimentalDsl::class)
    private val recipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebShopRecipe.recipe)

    class ObservedContext(
        val traceId: String,
        val spanId: String,
        val mdcTraceId: String?,
        val mdcSpanId: String?,
        val mdcRecipeInstanceId: String?
    )

    /** Records the context that is ambient while the interaction runs. */
    class RecordingValidateOrder(
        private val observed: ConcurrentHashMap<String, ObservedContext>,
        private val started: CountDownLatch
    ) : ValidateOrder {

        override fun apply(recipeInstanceId: String, order: String): ValidateOrder.ValidateOrderOutcome {
            // Make sure interactions of different recipe instances overlap on the shared pool.
            started.countDown()
            started.await(10, TimeUnit.SECONDS)

            val spanContext = Span.current().spanContext
            observed[recipeInstanceId] = ObservedContext(
                traceId = spanContext.traceId,
                spanId = spanContext.spanId,
                mdcTraceId = MDC.get("trace_id"),
                mdcSpanId = MDC.get("span_id"),
                mdcRecipeInstanceId = MDC.get("recipeInstanceId")
            )
            return ValidateOrder.OrderValid()
        }
    }

    @Test
    fun `concurrent executions keep their own trace inside interactions`() {
        val observed = ConcurrentHashMap<String, ObservedContext>()
        val started = CountDownLatch(concurrencyLevel)

        TracerFixture.use { fixture ->
            val baker = InMemoryBaker.java(
                BakerConfig.default(),
                ImmutableList.of(
                    ManufactureGoodsImpl(),
                    SendInvoiceImpl(),
                    ShipGoodsImpl(),
                    RecordingValidateOrder(observed, started),
                    LogRecipeFailedImpl()
                ),
                fixture.tracer
            )
            baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

            val recipeInstanceIds = (1..instanceCount).map { UUID.randomUUID().toString() }
            val executor = Executors.newFixedThreadPool(concurrencyLevel)
            try {
                recipeInstanceIds.mapIndexed { index, recipeInstanceId ->
                    executor.submit { runHappyFlow(baker, recipeInstanceId, "order-$index") }
                }.forEach { it.get(30, TimeUnit.SECONDS) }
            } finally {
                executor.shutdownNow()
            }

            val spans = fixture.exporter.finishedSpanItems
            assertEquals(instanceCount, observed.size, "Expected every execution to record its ambient context")

            val traceIdsPerInstance = recipeInstanceIds.associateWith { recipeInstanceId ->
                spans
                    .filter { it.attributes.get(AttributeKey.stringKey("baker.recipe.instance.id")) == recipeInstanceId }
                    .map { it.spanContext.traceId }
                    .toSet()
            }

            recipeInstanceIds.forEach { recipeInstanceId ->
                val context = observed[recipeInstanceId]
                assertNotNull(context, "Expected a recorded context for $recipeInstanceId")
                requireNotNull(context)

                assertTrue(
                    context.traceId != invalidTraceId,
                    "Expected a valid ambient span inside interaction of $recipeInstanceId"
                )

                val interactionSpan = spans.firstOrNull {
                    it.name == "baker.interaction.ValidateOrder" &&
                        it.attributes.get(AttributeKey.stringKey("baker.recipe.instance.id")) == recipeInstanceId
                }
                assertNotNull(interactionSpan, "Expected an interaction span for $recipeInstanceId")
                requireNotNull(interactionSpan)

                assertEquals(
                    interactionSpan.spanContext.spanId,
                    context.spanId,
                    "Span.current() inside the interaction of $recipeInstanceId must be its own interaction span"
                )
                assertEquals(interactionSpan.spanContext.traceId, context.traceId)

                val otherTraceIds = traceIdsPerInstance
                    .filterKeys { it != recipeInstanceId }
                    .values
                    .flatten()
                    .toSet()
                assertTrue(
                    !otherTraceIds.contains(context.traceId),
                    "Execution $recipeInstanceId observed a trace id that belongs to another execution"
                )
            }
        }
    }

    @Test
    fun `interaction mdc carries the trace of its own interaction span`() {
        val observed = ConcurrentHashMap<String, ObservedContext>()
        val started = CountDownLatch(concurrencyLevel)

        TracerFixture.use { fixture ->
            val baker = InMemoryBaker.java(
                BakerConfig.default(),
                ImmutableList.of(
                    ManufactureGoodsImpl(),
                    SendInvoiceImpl(),
                    ShipGoodsImpl(),
                    RecordingValidateOrder(observed, started),
                    LogRecipeFailedImpl()
                ),
                fixture.tracer
            )
            baker.addRecipe(RecipeRecord.of(recipe, System.currentTimeMillis(), false, true)).get()

            val recipeInstanceIds = (1..instanceCount).map { UUID.randomUUID().toString() }
            val executor = Executors.newFixedThreadPool(concurrencyLevel)
            try {
                recipeInstanceIds.mapIndexed { index, recipeInstanceId ->
                    executor.submit { runHappyFlow(baker, recipeInstanceId, "order-$index") }
                }.forEach { it.get(30, TimeUnit.SECONDS) }
            } finally {
                executor.shutdownNow()
            }

            recipeInstanceIds.forEach { recipeInstanceId ->
                val context = requireNotNull(observed[recipeInstanceId])
                assertEquals(context.traceId, context.mdcTraceId, "MDC trace_id must match the ambient span")
                assertEquals(context.spanId, context.mdcSpanId, "MDC span_id must match the ambient span")
                assertEquals(recipeInstanceId, context.mdcRecipeInstanceId, "MDC must carry the own recipe instance")
            }

            assertTrue(MDC.get("trace_id") == null, "Interaction MDC must not leak to the calling thread")
        }
    }

    private fun runHappyFlow(baker: Baker, recipeInstanceId: String, order: String) {
        val customerInfo = CustomerInfo("name", "address", "email")
        baker.bake(recipe.recipeId(), recipeInstanceId).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(OrderPlaced(order))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(CustomerInfoReceived(customerInfo))).get()
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(PaymentMade())).get()
        baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(30)).join()
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
                    tracer = openTelemetry.getTracer("test.inmemory.baker.concurrency")
                ).use(block)
            }
        }
    }
}
