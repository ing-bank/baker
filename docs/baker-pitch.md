# [fit]Complex Orchestration Logic is Hard to Change

---

## Baker
### Declare the Logic Like a Recipe
### Visualize the Logic
### Don't Worry About Retries and State

---

## Under the Hood
### DSL for Recipes
### Actor Model with Petri nets
### Event-Driven Architecture

---

## Up to 4x Faster Time to Market
## Less Incidents
## Business and IT Speak the Same Language

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

![fit](recipe.png)

---

```java
//notify Baker when events occur
baker.processEvent(processId, new SensoryEvents.IndividualInformationSubmitted(name, address));
baker.processEvent(processId, new SensoryEvents.TermsAndConditionsAccepted());
```

---

![fit](end-state.png)