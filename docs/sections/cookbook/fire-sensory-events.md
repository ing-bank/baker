# Fire events and inquiry

This section describes how to fire sensory events into a Baker process, and how to query information from a running
Baker process.

!!! Note
    For the Java API most methods return a `CompletableFuture<A>`, in the Scala API they return `Future<A>`. The Kotlin
    API makes use of `suspending` functions, and thus does not wrap the return type. To keep things readable,
    the descriptions in this section reason from Java's perspective.

## Fire sensory events

To trigger a Baker process you'll need to fire a sensory event. After firing an event, you may want to continue your 
asynchronous computation at one of the following moments:

1. Right after the event was received, but before any interactions are executed.
2. After all interactions have completed. At this point the process is either finished, or requires other sensory events to continue.
3. As soon one of the interactions fires a specific event.

To this end, the Baker interface exposes one method to fire an event and 2 methods to wait. We'll discuss each of those in more detail.

### Fire sensory event and wait for acknowledgement of it's reception.

This method completes right after the event was received, but before any interactions are executed. 

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/application/FireEventAndResolveWhenReceived.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/application/FireEventAndResolveWhenReceived.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/application/FireEventAndResolveWhenReceived.scala"
    ```

### Wait for completion

`awaitCompleted` completes when additional sensory events are required to continue
the process, or when the process has finished.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/application/FireEventAndResolveWhenCompleted.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/application/FireEventAndResolveWhenCompleted.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/application/FireEventAndResolveWhenCompleted.scala"
    ```

### Wait for an event

`awaitEvent` completes when an event with the specified name appears in the list of fired events. 

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/application/FireEventAndResolveOnEvent.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/application/FireEventAndResolveOnEvent.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/application/FireEventAndResolveOnEvent.scala"
    ```

## Inquiry
Baker allows you to query the state of a recipe instance at any given moment. To this end, Baker exposes a couple
of different methods that allow you to fetch information about events, ingredients, and interactions from a running process.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/application/InquiryExample.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/application/InquiryExample.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/application/InquiryExample.scala"
    ```