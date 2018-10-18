# Type system

The purpose of the type system is express the form of [ingredients](concepts#ingredient) in baker.

### Why not just use the java type system?

1. We want to garuantee that all data can be read back from persistent storage.

    This is for the benefit of being able to write generic analysis/data-mining tools on the persisted events.

2. We want to Baker as a service, receiving new recipes at runtime.

    Unless opting for OSGi or similar, you cannot load new class definitions. This makes it very impractical or impossible to depend on java classes.

## Interoptability with java types

Because it is impractical to directly work with the baker types in java/scala code there is conversion system.

## Default supported types

### java

- primitives and their boxed variants
- Enum types
- java.util.List
- java.util.Set
- java.util.Map
- java.math.BigInt
- java.math.BigDecimal
- java.util.Optional
- POJO classes

### scala

- primitives and their boxed variants
- case classes
- scala.collection.immutable.List
- scala.collection.immutable.Set
- scala.collection.immutable.Map
- BigInt
- BigDecimal
- scala.Option

## Registering a custom type adapter

All default type adapters are registered in the [reference.conf](https://github.com/ing-bank/baker/blob/master/bakertypes/src/main/resources/reference.conf) of the `baker-types` module.

You can add your custom type adapter by registering it in a `reference.conf`.

```
baker.types {

   "com.example.MyCustomType" = "com.example.MyCustomTypeAdpater"
}
```

For an example how to implement an adapter see [here](https://github.com/ing-bank/baker/blob/adf9b2edd4fe5ebdcec2bdd7f281cd151d64afe6/bakertypes/src/main/scala/com/ing/baker/types/modules/JavaModules.scala#L93)