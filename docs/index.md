# Baker

Baker is a library that provides a simple and intuitive way to orchestrate microservice-based process flows.

You declare your orchestration logic as a recipe using the Java, Kotlin, or Scala DSL. A recipe consists of
`interactions` (system calls), `ingredients` (data), and `events` (things that have happened in your process).

## Why Baker

Upgrading your business to an agile, adaptive and scalable microservice-based architecture can bring significant
advantages, but also critical challenges:

- Coupling of business logic to service technologies
- Inherent complexities of distributed systems

Baker solves these challenges by providing an expressive language to encode your business logic (recipe), and a
distributed runtime to scale recipe instances with little configuration and no extra development.

### Decouple business logic from your microservices 
Baker forces you to separate business logic from implementation details. Your business logic is expressed as a recipe
via the Java, Kotlin, or Scala DSL. The implementation details are contained in the interaction implementations.

### Ease the friction of distributed systems
When developing microservices you are confronted with all the inherent
challenges of distributed systems, topics like communication models, consistency decisions, handling failure, scaling
models, etc. Baker eases the development by providing out-of-the-box solutions from its clustered runtime. Baker nodes
are able to create and distribute recipe instances between them, handle failed interactions with several strategies,
restore the state of long-lived process and more.

### Reason about your business process without the burdens of technology
Baker can visualize your recipes, enabling developers and business stakeholders to better communicate and reason 
about the business processes.

## Where to go from here?
New to Baker? A good first step is to read more about Baker's [core concepts](sections/concepts). Afterward, you can
follow this quick [tutorial](sections/tutorial) to build your first Baker process.
