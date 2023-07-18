# Interaction execution

This section will give a basic explanation when baker will execute interactions in your Recipe.
For a more in depth information please see the [execution-semantics page](../reference/execution-semantics.md).

## When does Baker execute an interaction
Baker will execute an interaction when: 

1. All incoming ingredients are available 
2. All event preconditions are met.

After an interaction is executed it will 'consume' the ingredients and events. 
Interactions get their own copies of events/ingredients to consume. 
You do not have to worry about one interaction taking the ingredients away from another.

To execute an interaction again all incoming ingredients need to be provided again and the event preconditions need to be met again.

## Reprovider interactions
Interactions can be configured to be reprovider interactions. 
This means that after execution they will provide their own ingredients again. 
Reprovider interactions will only need to have their ingredients to be provided once. 
They will execute everytime their event preconditions are met.

Reprovider interactions do not update the ingredient data and will always use the latest ingredient data that is available.

If there are no event preconditions on a reprovider interaction, it will automatically loop its execution. Therefore this is made mandatory in the RecipeCompiler.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithReproviderInteraction.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithReproviderInteraction.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithReproviderInteraction.scala"
    ```