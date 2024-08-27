# Baker

Baker is a library that provides a simple and intuitive way to orchestrate microservice-based process flows.

You declare your orchestration logic as a recipe using the Java, Kotlin, or Scala DSL. A recipe consists of
`interactions` (system calls), `ingredients` (data), and `events` (things that have happened in your process).

## Why Baker

When working with microservice architectures, you encounter various challenges related to distributed systems. Things
like communication models, consistency management, failure handling, scaling approaches, and more. Baker simplifies
the development process by offering out-of-the-box solutions with its clustered runtime. Baker nodes can create and 
distribute instances of recipes, handle failures in interactions using different strategies, restore the state of 
long-lived processes, and provide additional functionalities to streamline microservice development.

??? Abstract "Service composition"
    Baker allows you to compose complex business processes by combining multiple microservices. It acts as a centralized
    control mechanism to define the sequence and dependencies between services. Facilitating the execution of
    orchestrated processes. Enabling you to build more robust and sophisticated applications that span multiple services.

??? Abstract "Decouple business logic from service technologies"
    Baker forces you to separate business logic from implementation details. Your business logic is expressed as a recipe
    via the Java, Kotlin, or Scala DSL. The implementation details are contained in the interaction implementations.

??? Abstract "Retry mechanism"
    Baker includes a built-in retry mechanism. When a failure occurs in a microservice, Baker can automatically retry 
    the failed operation. Retrying the operation can help overcome transient errors or temporary network issues. Baker 
    can be configured with retry policies, including parameters such as the number of retries, delay between retries, 
    and exponential backoff strategies.

??? Abstract "Visualize your business process"
    Bakers ability to visualize recipes provides a powerful communication tool that helps product owners, architects, and 
    engineers to have a common understanding of the business process. This feature allows you to easily share your 
    recipe with others, enabling collaboration and feedback.
    
## New to Baker?

A good first step is to read more about Baker's [core concepts](sections/concepts). Afterward, you can
follow this quick [tutorial](sections/tutorial) to build your first Baker process.
