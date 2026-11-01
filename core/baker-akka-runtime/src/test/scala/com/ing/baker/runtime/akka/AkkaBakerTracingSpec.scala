package com.ing.baker.runtime.akka

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.otel.BakerTraceAttributes
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.typesafe.config.ConfigFactory
import io.opentelemetry.api.common.AttributeKey
import io.opentelemetry.api.trace.{Span, StatusCode, Tracer}
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.`export`.SimpleSpanProcessor
import io.opentelemetry.sdk.trace.data.SpanData
import org.scalatest.BeforeAndAfterAll
import org.scalatest.flatspec.AsyncFlatSpecLike
import org.scalatest.matchers.should.Matchers
import org.slf4j.MDC

import java.util.UUID
import java.util.concurrent.atomic.AtomicReference
import java.util.concurrent.{ConcurrentHashMap, CountDownLatch, TimeUnit}
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.jdk.CollectionConverters._

object AkkaBakerTracingSpec {

  case class OrderPlaced(orderId: String, items: List[String])

  sealed trait ReserveItemsOutput
  case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

  val reserveItems: Interaction = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(Ingredient[String]("orderId"), Ingredient[List[String]]("items")),
    output = Seq(Event[ItemsReserved])
  )

  val recipe: Recipe = Recipe("AkkaBakerTracingRecipe")
    .withSensoryEvents(Event[OrderPlaced])
    .withInteraction(reserveItems)

  trait ReserveItems {
    def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput]
  }

  /** The ambient context observed while the interaction runs. */
  case class ObservedContext(traceId: String,
                             spanId: String,
                             mdcTraceId: String,
                             mdcSpanId: String,
                             mdcRecipeInstanceId: String)

  class RecordingReserveItems(observed: ConcurrentHashMap[String, ObservedContext],
                              started: AtomicReference[CountDownLatch]) extends ReserveItems {
    override def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput] = {
      // Makes interactions of different recipe instances overlap on the shared pool when a latch is installed.
      val latch = started.get()
      latch.countDown()
      latch.await(10, TimeUnit.SECONDS)

      val spanContext = Span.current().getSpanContext
      observed.put(orderId, ObservedContext(
        spanContext.getTraceId,
        spanContext.getSpanId,
        MDC.get("trace_id"),
        MDC.get("span_id"),
        MDC.get("recipeInstanceId")))
      Future.successful(ItemsReserved(items))
    }
  }

  class FailingReserveItems extends ReserveItems {
    override def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput] =
      throw new RuntimeException("reservation failed")
  }
}

/**
  * Verifies that the akka runtime emits the same spans as the in-memory runtime, and that the ambient tracing
  * context observed inside an interaction belongs to that very interaction, also under concurrency.
  */
class AkkaBakerTracingSpec
  extends Matchers
    with AsyncFlatSpecLike
    with BeforeAndAfterAll {

  import AkkaBakerTracingSpec._

  private val invalidTraceId = "00000000000000000000000000000000"

  private val exporter: InMemorySpanExporter = InMemorySpanExporter.create()

  private val tracerProvider: SdkTracerProvider =
    SdkTracerProvider.builder().addSpanProcessor(SimpleSpanProcessor.create(exporter)).build()

  private val tracer: Tracer =
    OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build().getTracer("test.akka.tracing")

  private val observed = new ConcurrentHashMap[String, ObservedContext]()

  private val instanceCount = 8

  private val started = new AtomicReference[CountDownLatch](new CountDownLatch(0))

  // Created lazily: scalatest instantiates every discovered suite up front, and an actor system plus a running
  // baker started at construction time competes with the other suites in this module.
  private lazy val system: ActorSystem = ActorSystem("AkkaBakerTracingSpec", ConfigFactory.load())

  private lazy val baker: Baker = {
    val interactions = CachingInteractionManager(List(
      InteractionInstance.unsafeFrom(new RecordingReserveItems(observed, started))))
    AkkaBaker(AkkaBakerConfig.localDefault(system, interactions).copy(tracer = tracer)(system))
  }

  private lazy val failingBaker: Baker = {
    val interactions = CachingInteractionManager(List(
      InteractionInstance.unsafeFrom(new FailingReserveItems)))
    AkkaBaker(AkkaBakerConfig.localDefault(system, interactions).copy(tracer = tracer)(system))
  }

  override def afterAll(): Unit = {
    tracerProvider.close()
    TestKit.shutdownActorSystem(system)
  }

  private def spansFor(recipeInstanceId: String): List[SpanData] =
    exporter.getFinishedSpanItems.asScala.toList.filter { span =>
      span.getAttributes.get(AttributeKey.stringKey(BakerTraceAttributes.RECIPE_INSTANCE_ID)) == recipeInstanceId
    }

  /** Baker events are published on the event stream, so spans may land slightly after the fire call returns. */
  private def awaitSpanNames(recipeInstanceId: String, expected: Set[String]): List[String] = {
    val deadline = System.currentTimeMillis() + 10000
    var names = spansFor(recipeInstanceId).map(_.getName)
    while (!expected.subsetOf(names.toSet) && System.currentTimeMillis() < deadline) {
      Thread.sleep(50)
      names = spansFor(recipeInstanceId).map(_.getName)
    }
    names
  }

  private def runHappyFlow(recipeId: String, recipeInstanceId: String, orderId: String): Future[Unit] =
    for {
      _ <- baker.bake(recipeId, recipeInstanceId)
      // `fireSensoryEventAndAwaitReceived` bypasses the SensoryEventResponseHandler and therefore never publishes
      // an EventReceived baker event, so the classic api is used here to observe the full set of spans.
      _ <- baker.fireEventAndResolveWhenReceived(recipeInstanceId,
        EventInstance.unsafeFrom(OrderPlaced(orderId, List("item1", "item2"))))
      _ <- baker.awaitCompleted(recipeInstanceId, timeout = 10.seconds)
    } yield ()

  "the akka runtime" should "emit lifecycle, event and interaction spans" in {
    val recipeInstanceId = UUID.randomUUID().toString
    val orderId = s"order-$recipeInstanceId"

    for {
      recipeId <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      _ <- runHappyFlow(recipeId, recipeInstanceId, orderId)
    } yield {
      val names = awaitSpanNames(recipeInstanceId,
        Set("baker.recipe-instance.created", "baker.event.received", "baker.event.fired", "baker.interaction.ReserveItems"))
      names should contain("baker.recipe-instance.created")
      names should contain("baker.event.received")
      names should contain("baker.event.fired")
      names should contain("baker.interaction.ReserveItems")
    }
  }

  it should "make the interaction span and its MDC ambient inside the interaction" in {
    val recipeInstanceId = UUID.randomUUID().toString
    val orderId = s"order-$recipeInstanceId"

    for {
      recipeId <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      _ <- runHappyFlow(recipeId, recipeInstanceId, orderId)
    } yield {
      val context = observed.get(orderId)
      context should not be null
      context.traceId should not be invalidTraceId
      context.mdcTraceId shouldBe context.traceId
      context.mdcSpanId shouldBe context.spanId
      context.mdcRecipeInstanceId shouldBe recipeInstanceId

      val interactionSpan = spansFor(recipeInstanceId).find(_.getName == "baker.interaction.ReserveItems")
      interactionSpan.map(_.getSpanId) shouldBe Some(context.spanId)
      interactionSpan.map(_.getTraceId) shouldBe Some(context.traceId)
    }
  }

  it should "keep concurrent executions on their own trace inside interactions" in {
    val recipeInstanceIds = (1 to instanceCount).map(_ => UUID.randomUUID().toString).toList
    started.set(new CountDownLatch(instanceCount))

    for {
      recipeId <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      _ <- Future.sequence(recipeInstanceIds.map { recipeInstanceId =>
        runHappyFlow(recipeId, recipeInstanceId, s"order-$recipeInstanceId")
      })
    } yield {
      val contexts = recipeInstanceIds.map(id => id -> observed.get(s"order-$id"))
      contexts.foreach { case (id, context) =>
        withClue(s"no ambient context recorded for $id: ") {
          context should not be null
        }
        context.traceId should not be invalidTraceId
        context.mdcRecipeInstanceId shouldBe id
        context.mdcTraceId shouldBe context.traceId
        context.mdcSpanId shouldBe context.spanId
      }

      // Every execution observed its own interaction span, so all span ids are distinct.
      contexts.map(_._2.spanId).distinct.size shouldBe instanceCount

      // The interaction span of an instance shares the trace of that instance's spans only.
      contexts.foreach { case (id, context) =>
        val traceIds = spansFor(id).map(_.getTraceId).toSet
        withClue(s"interaction trace of $id leaked into another instance: ") {
          traceIds should contain(context.traceId)
        }
        contexts.filterNot(_._1 == id).foreach { case (otherId, other) =>
          withClue(s"$id and $otherId observed the same interaction span: ") {
            other.spanId should not be context.spanId
          }
        }
      }
      succeed
    }
  }

  it should "record a failed interaction as an error span" in {
    val recipeInstanceId = UUID.randomUUID().toString

    for {
      recipeId <- failingBaker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
      _ <- failingBaker.bake(recipeId, recipeInstanceId)
      _ <- failingBaker.fireEventAndResolveWhenReceived(recipeInstanceId,
        EventInstance.unsafeFrom(OrderPlaced(s"order-$recipeInstanceId", List("item1"))))
    } yield {
      // The interaction blocks on failure, so the span is awaited instead of the recipe completing.
      awaitSpanNames(recipeInstanceId, Set("baker.interaction.ReserveItems"))

      val interactionSpan = spansFor(recipeInstanceId).find(_.getName == "baker.interaction.ReserveItems")
      interactionSpan.map(_.getStatus.getStatusCode) shouldBe Some(StatusCode.ERROR)
      interactionSpan.map(_.getAttributes.get(AttributeKey.stringKey(BakerTraceAttributes.ERROR_TYPE))) shouldBe
        Some(BakerTraceAttributes.INTERACTION_FAILURE)
    }
  }
}
