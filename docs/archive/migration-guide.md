# Migration Guide

## From 1.3.x to 2.0.0

This guide only describes how to migrate your existing application.

Summary:

- *ALL* persisted data from baker `1.3.x` *IS COMPATIBLE* and can be used with `2.0.x`
- When running a cluster *DOWNTIME IS REQUIRED* because of binary incompatible changes in the message protocol.
- Some small code refactors are necessary (see below).

For a full list new features see the [changelog](https://github.com/ing-bank/baker/blob/master/CHANGELOG.md).

### Downtime required for clusters with state

In `2.0.0` some binary incompatible changes where made in the message protocol.

This requires you to bring down the entire cluster (`1.3.x`) and bring it up again (`2.0.0`).

A rolling deploy *IS NOT* tested and *NOT* recommended.

### Removed Ingredient interface

`com.ing.baker.recipe.javadsl.Ingredient` was removed.

This was a tagging interface that was not used in the project.

You can remove all references to this interface in your project.

One thing to note is that `Ingredient` extended from `scala.Serializable`.

If you depended on this behaviour just replace `Ingredient` by `scala.Serializable`.

### @ProvidesIngredient removed

In `1.3.x` you could directly provide an ingredient from an interaction. For example:

``` java

import com.ing.baker.recipe.annotations.ProvidesIngredient;

interface GetEmail {

  @ProvidesIngredient("email")
  String apply(@RequiresIngredient("customer") Customer customer);
}

```

This feature has been removed. Internally this was already translated to an implicitly generated event: `$interactionName + Successful`.

Now it is required that you do this expclitly to avoid confusion.

The refactor is very straight forwfard:

``` java
import com.ing.baker.recipe.annotations.FiresEvent;

interface GetEmail {

  public class GetEmailSuccessful {
    public final String email;
    public ExampleInteractionSuccessful(String email) {
      this.email = email;
    }
  }

  @FiresEvent(oneOf = { GetEmailSuccessful.class } )
  GetEmailSuccessful apply(@RequiresIngredient("customer") Customer customer);
}

```

If you use [lombok](https://projectlombok.org) annotations you can get rid of a lot of the boiler plate by using `@Value` on the event class.

In `scala` it is recommended to use case classes.

