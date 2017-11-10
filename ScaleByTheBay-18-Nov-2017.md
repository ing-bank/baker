slidenumbers: true
autoscale: true

# Declare, verify and execute microservices-based process flows with Baker
## Scale By the Bay 2017, San Francisco
### Nikola Kasev | ING Bank

---

![](poffertjes.jpeg)

---

## Symptoms of a Failing Application Architecture

---

![original](afraid.jpg)
## Afraid to change the application code

---

![original](breaks.jpg)
## Functionality breaks unexpectedly

---

![original](time-to-market.jpg)
## Slow time to market

---

## How to turn this around?

---

![](gordon-ramsay.jpg)

---

![](simplify.jpg)

---
	
![](fresh.jpg)

---
	
![](communicate.jpg)

---

![](baker-github.png)

---

![left](simplify.jpg)

## Simplify
### Domain Specific Language for orchestration flows
### Declarative
### Easy to change

---

![left](fresh.jpg)

## Reuse
### Recipes
### Interactions
### Ingredients
### Events

---

![left](communicate.jpg)

## Communicate
### Visualize your code
### Non-IT understand as well
### Reason About Comfortably

---

## Design-time

---

```scala
val registerIndividual = Interaction(
  name = "RegisterIndividual",
  inputIngredients = Seq.empty,
  output = FiresOneOfEvents(registerIndividualSuccessful, registerIndividualFailed)
)
```

---

```scala
val registerIndividual = Interaction(
  name = "RegisterIndividual",
  inputIngredients = Seq.empty,
  output = FiresOneOfEvents(registerIndividualSuccessful, registerIndividualFailed)
)
```

---

![](individual.png)

---

![](account.png)

---

![](assign.png)

---

```scala
val openAccountRecipe = Recipe("OpenAccountRecipe")
  .withInteractions(
    assignAccount,
    getAccount,
    registerIndividual)
```

---

![fit](recipe-no-sensory.png)

---

```scala
val openAccountRecipe = Recipe("OpenAccountRecipe")
  .withInteractions(
    assignAccount,
    getAccount.withRequiredEvent(termsAndConditionsAccepted),
    registerIndividual)
  .withSensoryEvents(
    termsAndConditionsAccepted,
    individualInformationSubmitted)
```

---

![fit](recipe.png)

---

## Run-time

---

```scala
//for each process instance, bake the recipe
baker.bake(processId);
//notify Baker when events occur
baker.processEvent(processId, individualInformationSubmitted.instance(name, address));
baker.processEvent(processId, termsAndConditionsAccepted.instance());

//retrieve ingredients stored in the accumulated state
assert(baker.getIngredients(processId).get("customerId").equals(customerId));
assert(baker.getIngredients(processId).get("iban").equals(iban));

//retrieve all events that have occurred
baker.events(processId)
```

---

![fit](end-state.png)

---

## Under the Hood

---	

### Why Scala?

- Best fit for developing DSLs[^1] on the JVM
- Compile-time recipe validation
- Type safety

[^1]: https://martinfowler.com/books/dsl.html

---

### Why Akka?

- Event Sourcing[^2] (events can be replayed)
- Persistent actors (with Cassandra)
- Distributed actors across machines (with cluster sharding)

[^2]: http://martinfowler.com/eaaDev/EventSourcing.html

---



## Best Practices

---

### Short-lived vs. long-running flows

---

### State is taken care of:

- Cassandra for persistent storage
- Ingredients encrypted by default
- State recovered automatically

---

### Run Baker inside of your API
### "Smart endpoints and dumb pipes"

---

### When failure occurs:

- Baker retries technical failures with exponential backoff
- Works well with **idempotent** services
- Deal with functional failure in your recipe

---

Baker Capability Matrix:

- Investigate not one, not two, but **all business processes** in your company
- Where do you see re-use?
- Map using MoSCoW[^4] to give importance (M = 10, S = 5, C = 2, W = 1)

[^4]: https://en.wikipedia.org/wiki/MoSCoW_method

---

| Checking Account | Savings Account | Customer Onboarding |
| :--- | :---: | ---: |
| Verify Identity | Verify Identity | Verify Identity |
| Register Individual | Register Individual | Register Individual |
| Open *Checking* Account | Open *Savings* Account | `n/a` |
| Issue Debit Card | `n/a` | `n/a` |
| Send Message | Send Message | Send Message |
| Register Product Owner | Register Product Owner | `n/a` |

---

![](call-to-action.jpg)
## https://github.com/ing-bank/baker

---

![](pbt.png)

---

### Why Petri net?[^3]

[^3]: https://en.wikipedia.org/wiki/Petri_net

---

![](reachability.png)

---

![](unreachable.png)

---

![](dead-code.png)


---

![](path.png)

---

![](bottleneck.png)

---

**I love cooking food** and for the rest of the talk I'll be using analogies from there. It's very **similar to our industry**: long hours, hard work, and delivering experiences to our customers.

Have you been woken up at 3 o'clock in the morning on a **Saturday morning** after a night of partying, having to go to the war room and resolve an application incident. I've been there. When I remember the cold of the **airconditioners**, it still **makes me shiver**.

If we are building microservices or a monolith or any type of application in general we are **serving business logic to our clients**. So no matter what, we cannot escape the **architectural discussion**. If we are not careful of how we architect our applications we end up serving a bad meal to our clients.



