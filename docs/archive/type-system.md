# Type system

The purpose of the type system is express the form of [ingredients](concepts.md#ingredient) in baker.

### Why not use the java type system?

1. To garuantee that all data can be read back from persistent storage.

    This is for the benefit of being able to write generic analysis/data-mining tools on the persisted events.

2. To run Baker As A Service, receiving new recipes at runtime.

    Unless opting for OSGi or similar, you cannot load new class definitions. This makes it very impractical or impossible to depend on java classes.

The main concepts in this type system are *Types* and *Values*.

An important difference from type systems in programming languages is that *Values* do **not** have
an explicit inherint type associated with them.

You can argue whether you can call this a type system at all. Perhaps a schema system is more accurate.

## Types

### Primitives

| Type | Java parallel | Description |
| --- | --- | --- |
| `Bool` | `boolean` | *single* bit, `true` or `false`, `1` or `0` |
| `Char` | `char` | Unsigned `16` bit integer |
| `Byte` | `byte` | Signed `8` bit integer |
| `Int16` | `short` | Signed `16` bit integer |
| `Int32` | `int` | Signed `32` bit integer |
| `Int64` | `long` | Signed `64` bit integer |
| `IntBig` | `BigInteger` | Integer of arbitrary size |
| `Float32` | `float` | Signed `32` bit floating point |
| `Float64` | `double` | Signed `64` bit floating point |
| `FloatBig` | `BigDecimal` | Floating point of arbitrary size |
| `Date` | `long` | A *UTC* date in the *ISO-8601* calendar system with *millisecond* precision |
| `ByteArray` | `Array<Byte>` | Byte array, often used for binary data |
| `CharArray` | `String` | Character array, or commmonly called `String` |

### Structured types

| Type | Java parallel | Description |
| --- | --- | --- |
| `ListType<T>` | `java.util.List<T>` | A list of values, all of the same type |
| `OptionType<T>` | `java.util.Optional<T>` | Matches against `T` or `null` |
| `EnumType` | `enum class` | A set of predifined options (strings) |
| `RecordType` | `POJO class` | A record with a specific set of fields |
| `MapType<T>` | `java.util.Map<String, T>` | A record with arbitrary fields, all of the same type |

## Values

Values are pure data without any direct associated type. These very closely match the *JSON* data format.

| Value | Description |
| --- | --- |
| `NullValue` | Analogues to `null`, `Optional.empty`, `None`, etc ... |
| `PrimitiveValue` | Wrapper for for: <br/>- A Java primitive (or boxed variant)<br/> - `java.lang.String`<br/> - `java.math.BigInteger`<br/> - `java.math.BigDecimal`<br/> - `scala.math.BigInt`<br/> - `Array<Byte>`|
| `ListValue` | A list of values |
| `RecordValue` | A set of `String -> Value` pairs |

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