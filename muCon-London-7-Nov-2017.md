slidenumbers: true
autoscale: true
# Declare, verify and execute microservices-based process flows with Baker

---

![](dirty-kitchen.jpg)

---

![](poffertjes.jpeg)

---

## Symptoms of a Failing Restaurant

---

![](slow.jpg)

---
	
![](garbage.jpg)

---

![](enjoyable.jpg)

---

## Symptoms of a Failing (Microservices) Architecture

---

* We are afraid to change the code
* Functionality breaks unexpectedly
* Slow time to market

---

## How to Turn a "Hell's Kitchen" into a Successful Restaurant?

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

```[.highlight: 1,6,7]
public interface RegisterIndividual extends Interaction {
    @FiresEvent(oneOf = {RegisterIndividualSuccessful.class,
            RegisterIndividualFailed.class})
    RegisterIndividualOutcome apply(
            @ProcessId String processId,
            @RequiresIngredient("name") String name,
            @RequiresIngredient("address") String address
    );
}

```

---

```[.highlight: 2,3]
public interface RegisterIndividual extends Interaction {
    @FiresEvent(oneOf = {RegisterIndividualSuccessful.class,
            RegisterIndividualFailed.class})
    RegisterIndividualOutcome apply(
            @ProcessId String processId,
            @RequiresIngredient("name") String name,
            @RequiresIngredient("address") String address
    );
}

```

---

![](individual.png)

---

![](account.png)

---

![](assign.png)

---

```java, [.highlight: 3-6]
public Recipe get(){
    return new Recipe("MuConf2017Demo").
            withInteractions(
                    of(AssignAccount.class),
                    of(GetAccount.class),
                    of(RegisterIndividual.class));
}
```

---

![fit](recipe-no-sensory.png)

---

```java, [.highlight: 5, 7-9]
return new Recipe("MuConf2017Demo").
        withInteractions(
                of(AssignAccount.class),
                of(GetAccount.class).
                        withRequiredEvent(TermsAndConditionsAccepted.class),
                of(RegisterIndividual.class)).
        withSensoryEvents(
                TermsAndConditionsAccepted.class,
                IndividualInformationSubmitted.class);
}
```

---

![fit](recipe.png)

---

## Run-time

---

```java, [.highlight: 2,4,5,8,9,13]
//for each process instance, bake the recipe
baker.bake(processId);
//notify Baker when events occur
baker.processEvent(processId, new SensoryEvents.IndividualInformationSubmitted(name, address));
baker.processEvent(processId, new SensoryEvents.TermsAndConditionsAccepted());

//retrieve ingredients stored in the accumulated state
assert(baker.getIngredients(processId).get("customerId").equals(customerId));
assert(baker.getIngredients(processId).get("iban").equals(iban));

//retrieve all events that have occurred
Set<String> occurredEvents = new HashSet<>(
        baker.getEvents(processId).getEventNameList()
);
```

---

## Under the Hood

---	

Speed of change matters to anyone building software. Many engineering teams have identified Microservices as an important component of this architectural approach to designing more flexible systems that can meet the needs of their fast changing businesses. Applying this approach however, is hard. And ideas and practices are still very much evolving. To help with that, we've launched muCon - a conference to learn about emerging technologies and approaches, share challenges and evolve practices and ideas.

---

Their applications are built on top of microservices. If there careful enough their application serve bad meals. 

If we are building microservices or a monolith or any type of service in general we are serving business logic to our clients. So no matter what we can not escape the architectural discussion.
If we are not careful of how we architect our applications we end up serving bad meals.

---

**I love cooking food** and for the rest of the talk I'll be using analogies from there. It's very **similar to our industry**: long hours, hard work, and delivering experiences to our customers.

Have you been woken up at 3 o'clock in the morning on a **Saturday morning** after a night of partying, having to go to the war room and resolve an application incident. I've been there. When I remember the cold of the **airconditioners**, it still **makes me shiver**.

If we are building microservices or a monolith or any type of application in general we are **serving business logic to our clients**. So no matter what, we cannot escape the **architectural discussion**. If we are not careful of how we architect our applications we end up serving a bad meal to our clients.



