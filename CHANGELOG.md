# Changelog

## 1.0.9

- Changed serialization mechanism to allow custom akka serializers for ingredients where before only kryo was used.

  You might see these messages for ingredient types without bindings:

  Ingredient 'foo' of type 'com.example.Foo' cannot be serialized
  Please add a binding in your application.conf like this:
  akka.actor.serialization-bindings {
    "com.example.Foo" = kryo
  }

## 1.0.8
- Added the functionality that if an Ingredient of Java Optional or Scala Option is needed but not provided its provided as empty.
- Side note (no impact for baker users): kagara library is merged into baker, therefore baker has 2 new artifacts now: petrinet-api and petrinet-akka.
- slf4j MDC field 'kageraEvent' is renamed to 'petrinetEvent' due to new petrinet modules in baker.
- If io.kagera packages are used/imported in your application (maybe in logback files), you need to change them as com.ing.baker.petrinet 
- baker.conf file disables java serialization, you don't need to have 'akka.actor.allow-java-serialization = off' setting anymore in your application.conf files

## 1.0.7
- In your application.conf files, it is mandatory to include also baker.conf file which will set some sensible defaults for baker.
```
include "baker.conf"
```

## 1.0.6
- Using a better consistent hash function for place/transition identifiers in the petri net
- IMPORTANT: This change is not backwards compatible, on going processing cannot be resumed after a restart

## 1.0.4
- Migrated to akka 2.5.x
- A local event bus is implemented so that a listener can be registered to act on baker events. Ex:
```scala
      baker.registerEventListener(new EventListener {
        /**
          * Called when an event occurred.
          *
          * @param processId The process id for which the event occurred.
          * @param event     The event.
          */
        override def processEvent(processId: String, event: RuntimeEvent): Unit = ???
      })
```

## 1.0.1
- Fixed a bug in the runtime that it could not bind an ingredient multiple times as parameter for an interaction
- Removed the JCompiledRecipe and moved the functionality to the CompiledRecipe
- Added a validation to the java Recipe that @sFiresEvent and @ProvidesIngredient are not used at the same time.

## 1.0.0
- baker modules are reorganized to support mode modularity and loose coupling
- created separate modules: compiler, intermediate-language, recipe-dsl, runtime
- design time and runtime parts of baker are now separate and ideally could be updated independently

## 0.2.19
- enabled kryo serialization for all baker events that extend from com.ing.baker.api.Event interface
- disabled default Java serialization
- IMPORTANT: It is mandatory to extend/implement com.ing.baker.api.Event interface in your event classes. Kryo serialization understands plain pojo classes, so you may continue using lombok annotations
- IMPORTANT: It is mandatory to extend/implement com.ing.baker.api.Ingredient interface in your custom Ingredient data types. Kryo serialization understands all standard Java/Scala data types + guava + jodatime types.

## 0.2.16
- clients of baker can use protocol buffers serialized events with a proper protobuf configuration 
- bug fix in the passivation logic

## 0.2.15
- bug fix for the actor passivation logic

## 0.2.14
- bug fixes related to akka sharding

## 0.2.13
- Baker can now persist encrypted ingredients if enabled. This feature is disabled by default.
  
  To enable encryption you need to have the following two settings in your application.conf file.
  ```
  baker.encryption.enabled = on
  baker.encryption.secret = someStrongSecretText
  ```

## 0.2.6
- Now allow the adding of Events that have no ingredients nor have any preconditions.
  For these events a dummy ingredient is created to allow it to be added to the petri net.
  This dummy ingredient is filtered out during visualisation of the recipe.

## 0.2.5
- Fixed a bug in visualisation of a recipe that had max interaction count.

## 0.2.4
- JBaker now expects a List\<Interaction\> instead of List\<JInteraction\>
- Sieves do not need to have a implementation added anymore
- Added a check to the recipe compilation to check if a Sieves have a default constructor

## 0.2.3
- Allowed changing the Interaction name in the JInteractionDescriptor
- By changing a interaction name now multiple of the same interaction are allowed in a recipe

## 0.2.2
- Baker and JBaker now expect a List\<JInteraction\> instead of a List\<Object\> for the implementations
