# CompletableFuture Migration Plan for In-Memory Runtime - Phases 4 and 5

## Context

Phases 2 and 3 isolate most in-memory runtime effect wiring behind local adapters and start incremental replacement.
This document captures the remaining work to move from "adapter-based IO internals" to "first-class CompletableFuture backend".

## Phase 4 - Core Model Convergence

### Goal

Make shared runtime abstractions in `../../core/baker-interface` backend-neutral so in-memory runtime can run on `CompletableFuture` without relying on `cats-effect` semantics.

### Why this is hard

Today the runtime depends on semantics not provided by plain `CompletableFuture`, including:

- cancellation and fiber lifecycle (`start`, `uncancelable`, `onCancel` semantics)
- race/timeout behavior with deterministic fallback semantics
- effectful stream execution (`fs2.Stream[F, A]` requires strong `Async[F]` capabilities)
- non-blocking wait primitives used in `RecipeInstanceManager` coordination paths

### Scope

1. **Effect capability split**
   - Audit `AsyncSupport`, `SyncSupport`, `Fs2Support`, `RefSupport` and classify required operations.
   - Split contracts into:
     - minimal synchronous core (`map`, `flatMap`, `delay`, `raiseError`)
     - async timing core (`sleep`, `timeoutTo`)
     - background execution core (`startAndForget`)
     - stream/runtime core (currently fs2-dependent)
   - Remove accidental dependency on full Cats `Async` where only minimal capability is needed.

2. **Runtime abstraction for streaming**
   - Introduce a small runtime interface for event propagation/execution pipelines (replace direct `fs2.Stream` leakage from model internals).
   - Keep fs2 implementation as one backend.
   - Add a second backend that uses Java async primitives (`CompletableFuture`, queues, schedulers) where feasible.

3. **Ref/state abstraction hardening**
   - Refactor stateful paths in `recipeinstance` package to rely only on local abstractions (not direct Cats constraints).
   - Ensure listener signaling (`awaitEvent`, `awaitCompleted`) does not assume fiber cancelation behavior unavailable in `CompletableFuture`.

4. **Timeout and scheduler unification**
   - Centralize timeout/sleep/scheduled retry in one backend-aware scheduler adapter.
   - Guarantee existing behavior for:
     - retry backoff
     - retention cleanup
     - await timeouts

5. **Error/cancellation semantics spec**
   - Add a behavior spec doc (and tests) that defines expected behavior for:
     - timeout errors
     - exceptional completion
     - cancellation during long-running interactions
     - listener notification guarantees

### Deliverables

- New backend-neutral effect interfaces in `../../core/baker-interface`.
- fs2/Cats backend implementation retained.
- CompletableFuture backend implementation added.
- Test matrix that runs model-level behavior tests on both backends for parity.

### Risks

- Behavior regressions around retries and races.
- Subtle ordering differences in listener and stream/event publication.
- Potential blocking if backend adapters accidentally use `.join()` in hot paths.

### Suggested verification gates

- `BakerModelSpec` parity pass for both backends.
- cleanup and await timing specs with repeated retries.
- stress test for concurrent event firing and blocked interaction resolution.

## Phase 5 - Decommission IO-Only In-Memory Internals

### Goal

Switch in-memory runtime default backend to CompletableFuture-native internals and retire IO-only internals.

### Scope

1. **Backend switch in in-memory builder**
   - Move `InMemoryBaker` internal default from IO-based components to CompletableFuture-based components.
   - Keep compatibility adapter for old IO build path during deprecation window.

2. **API transition strategy**
   - Keep existing APIs source-compatible for one deprecation window.
   - Mark IO-centric builder APIs as deprecated with explicit migration guidance.
   - Keep `javaAsync(...)` / CF entry points as preferred path.

3. **Cleanup of transitional adapters**
   - Remove duplicate conversion logic once all internal calls are backend-native.
   - Remove temporary bridge helpers no longer needed.

4. **Performance and memory validation**
   - Benchmark pre/post migration for:
     - bake + fire event throughput
     - idle/retention cleanup overhead
     - blocked interaction retry loops
   - Validate no scheduler/thread leaks across repeated runtime start/stop.

5. **Documentation and examples refresh**
   - Update docs and examples to default to CompletableFuture usage.
   - Add migration notes for teams still using IO-centric construction paths.

### Exit criteria

- No direct in-memory runtime dependency on `cats-effect` types in production code paths.
- Full behavior parity test suite passes.
- Benchmarks show no unacceptable regression.
- Deprecated APIs documented with target removal release.

## Rollout recommendation

- Release behind feature flag or alternate builder first.
- Run one release cycle with dual backend support.
- Remove legacy path only after adoption and parity confidence are confirmed.

