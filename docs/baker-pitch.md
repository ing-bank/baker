# [fit] Orchestration Logic is Hard to Change

---

## Baker is a Java Library
### Declare the Logic Like a Recipe
### Visualize the Logic
### Don't Worry About Retries and State

---

![fit](recipe.png)

---

## Rapid Time to Market
## Less Incidents
## Business and IT Speak the Same Language

---

## Under the Hood
### DSL for Recipes
### Actor Model with Petri nets
### Event-Driven Architecture

---

```java, [.highlight: 3,4,6]
return new Recipe("DemoAtTwitterHQ").
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

```java
//notify Baker when events occur
baker.processEvent(processId, new SensoryEvents.IndividualInformationSubmitted(name, address));
baker.processEvent(processId, new SensoryEvents.TermsAndConditionsAccepted());
```

---

![fit](end-state.png)