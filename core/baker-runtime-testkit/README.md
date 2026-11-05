# Baker Runtime Testkit

This module hosts runtime-agnostic test contracts and fixtures shared by:

- `core/baker-akka-runtime`
- `core/baker-pekko-runtime`

## Goal

Keep behavior tests in one place and provide only thin runtime-specific adapters in each runtime module.

## Usage Pattern

1. Put reusable test traits under `src/test/scala/com/ing/baker/runtime/testkit`.
2. Publish them as a `test-jar` from this module.
3. In runtime modules, create small specs that mix in a runtime adapter plus shared contracts.

## Next Migration Step

Migrate one duplicated Akka/Pekko spec pair first (for example execution semantics), validate, then continue in batches.

