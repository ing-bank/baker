# Effect Abstraction Contract (`runtime.model`)

This module keeps effect-system coupling out of `com.ing.baker.runtime.model` as much as possible.

## Rule

Code in `../core/baker-interface/src/main/scala/com/ing/baker/runtime/model` should depend on runtime support traits from `com.ing.baker.runtime.common`, not directly on Cats Effect types.

Use:

- `SyncSupport[F]` for pure/map/flatMap/error/delay/blocking operations
- `AsyncSupport[F]` for async, sleep, timeout, fire-and-forget, eager trigger points
- `RefSupport[F]` + `RefState[F, A]` for mutable state handles

Avoid in `runtime.model`:

- direct imports of `cats.effect.*`
- direct calls such as `unsafeRunSync`
- concrete effect checks/casts (for example, `isInstanceOf[IO[_]]`)

## Notes

- `AsyncSupport.eager` exists for places that require eager trigger behavior for specific runtimes (for example `IO`).
- `fs2.Stream` can still appear in model APIs where streaming is a public contract.

## Scope

This is a local contract for the `baker-interface` module and can be tightened further over time.

