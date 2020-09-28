# Monitor

To monitor a Baker application we recommend doing so by using the `baker.registerEventListener(recipeName?, listenerFunction)`
and the `baker.registerBakerEventListener(listenerFunction)`. The former can notify of every `EventInstance` that is being
fired globally or per `CompiledRecipe`. And the latter notifies of baker operations that happen like new `InteractionInstances` 
being executed or failing. These accept a function that can call your logging or metrics system:

=== "Scala (Recipe Events)"

    ```scala 
    baker.registerEventListener((recipeInstanceId: String, event: EventInstance) => {
      println(s"Recipe instance : $recipeInstanceId processed event ${event.name}")
    })
    ```

=== "Java (Recipe Events)"

    ```java 
    BiConsumer<String, EventInstance> handler = (String recipeInstanceId, EventInstance event) ->
        System.out.println("Recipe Instance " + recipeInstanceId + " processed event " + event.name());
        
    baker.registerEventListener(handler);
    ```

=== "Scala (Baker Events)"

    ```scala 
    import com.ing.baker.runtime.scaladsl._

    baker.registerBakerEventListener((event: BakerEvent) => {
      event match {
        case e: EventReceived => println(e)
        case e: EventRejected => println(e)
        case e: InteractionFailed => println(e)
        case e: InteractionStarted => println(e)
        case e: InteractionCompleted => println(e)
        case e: ProcessCreated => println(e)
        case e: RecipeAdded => println(e)
      }
    })
    ```

=== "Java (Baker Events)"

    ```java 
    import com.ing.baker.runtime.javadsl.BakerEvent;

    baker.registerBakerEventListener((BakerEvent event) -> System.out.println(event));
    ```

