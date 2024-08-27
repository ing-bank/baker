# Monitoring

Baker allows you to register a couple of different event listeners. These are especially useful for monitoring and
logging purposes.

!!! Warning
    Each event is guaranteed to be delivered `AT MOST ONCE`. You should not use an event listener for critical functionality.

!!! Note
    The delivery is local (JVM) only. You will not receive events from other nodes when running in cluster mode.

## Recipe instance events
The `registerEventListener` method allows you to declare an event listener which listens to all events of a specific
recipe instance.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/application/RegisterEventListener.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/application/RegisterEventListener.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/application/RegisterEventListener.scala"
    ```

## All Baker events
The `registerBakerEventListener` method allows you to declare an event listener which listens to all Baker events. These
are events that notify what Baker is doing.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/application/RegisterBakerEventListener.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/application/RegisterBakerEventListener.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/application/RegisterBakerEventListener.scala"
    ```