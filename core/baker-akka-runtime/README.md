# baker-akka-runtime

The akka based Baker runtime. `AkkaBaker` implements the Baker interface on top of the actors in
`baker-akka-actors`, with persistence, passivation and (optionally) clustering.

## OpenTelemetry tracing

The akka runtime emits the same spans as the in-memory runtime. Tracing is always on; without a configured
OpenTelemetry SDK the global tracer is a no-op and costs nothing.

### What is traced

- Recipe lifecycle: `baker.recipe-instance.created`
- Event flow: `baker.event.received`, `baker.event.fired`
- Interaction execution: `baker.interaction.<interactionName>`

Interaction spans are created as children of the latest event span for the same recipe instance.

### Ambient context inside interactions

The interaction span and the SLF4J `MDC` are installed on the very thread that invokes the interaction
implementation, so `Span.current()` belongs to *that* invocation, also under heavy concurrency:

```scala
class ReserveItemsImpl extends ReserveItems {
  override def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput] = {
    Span.current().addEvent("reserving") // the baker.interaction.ReserveItems span
    log.info("reserving")                // MDC contains trace_id, span_id and recipeInstanceId
    ...
  }
}
```

Interactions run on a shared pool. Before and after every invocation the registered context propagators are
cleared, so a pooled thread can never expose the context of a previous execution. If your interaction spawns its
own threads, propagate the context explicitly (for example with `Context.current().wrap(runnable)`).

For a `CompletionStage`-returning interaction the span is ended when the stage completes. For an interaction
returning a `scala.concurrent.Future` the span covers the synchronous part of the invocation only, because the
future is created inside the span scope but completes afterwards.

### Attributes

Identical to the in-memory runtime: `baker.recipe.id`, `baker.recipe.name`, `baker.recipe.instance.id`, plus,
depending on the span, `baker.event.name`, `baker.interaction.name`, `baker.correlation.id` and `error.type`.

### Injecting a custom tracer

By default `AkkaBakerConfig` uses `GlobalOpenTelemetry.getTracer("com.ing.baker.runtime.akka.AkkaBaker")`:

```scala
val tracer = GlobalOpenTelemetry.getTracer("my-service.baker")
val baker = AkkaBaker(AkkaBakerConfig.localDefault(system, interactions).copy(tracer = tracer)(system))
```

### Limitations

- The interaction instrumentation is published through the `BakerInstrumentation` akka extension, which is scoped
  to the `ActorSystem`. Running several `AkkaBaker` instances on one `ActorSystem` means the last one created wins
  for interaction spans. One baker per actor system is the supported setup.
- The recipe instance to trace-context mapping is node local, so in a cluster an interaction span is parented to
  the event span only when both happen on the node hosting the process instance actor.
- `fireSensoryEventAndAwaitReceived` does not publish an `EventReceived` baker event at all (it bypasses the
  `SensoryEventResponseHandler`), so no `baker.event.received` span is emitted for that api. The
  `fireEventAndResolveWhenReceived` family does emit it.

### Where the OpenTelemetry code lives

In `baker-interface-otel`, shared with the in-memory runtime. See `core/baker-interface-in-memory/README.md`
for the description of the SPIs that keep `baker-interface` itself free of OpenTelemetry.
