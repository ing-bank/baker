# Interactions

## Defining

You define an [interaction](../concepts#interaction) with a java interface. An example:

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

To be used as an interaction the interface requires an `apply` method with some restrictions.

* The method **must** be annotated with ``@FiresEvent`

* *ALL* arguments **must** be annotated:

    `@Named` or `@RequiresIngredient` are used for ingredient data that the interaction requires, the *name* must be specfied.

    `@ProcessId` is used for injecting the [process id](dictionary.md#process-id).

* The output classes have the same [restrictions](recipe-dsl.md#sensory-events) as sensory events.

## Implementation

Implementation is just implementing the interface. Nothing to explain here.