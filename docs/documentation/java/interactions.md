# Interactions

## Defining

You define an [interaction](../concepts#interaction) with a java interface. For example:

``` java
package com.example;

import com.ing.baker.recipe.annotations.*;
import javax.inject.Named;

public interface ValidateOrder {

    interface Outcome { }

    class Failed extends Outcome { }

    class Valid extends Outcome { }

    @FiresEvent(oneOf = {Failed.class, Valid.class})
    Outcome apply(@ProcessId String processId,
                  @Named("order") String key);
}
```

To be interpreted as an interaction the interface requires an `apply` function with some restrictions.

* The method **must** be annotated with @FiresEvent

* All arguments **must** be annotated with either `@Named`, `@RequiresIngredient`, `@ProcessId`

    `@Named` and `@RequiresIngredient` are used for ingredient data that the interaction requires, the *name* must be specfied.

    `@ProcessId` is used for injecting the process instance id.

## Implementation

Implementation is just implementing the interface. Nothing to explain here.