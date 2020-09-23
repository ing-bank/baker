# Baker Types and Values

Because of the distributed nature of Baker and how the runtime works, we need to have serializable types and values to 
transfer recipes and data between nodes and to match over such data, that is why we implemented a type system on top of Scala.
They help not just to model your domain but also for Baker to identify when to execute interactions. 

If you are using all of our reflection APIs then you will not use them directly, but it is good to know of their 
existence.

=== "Scala"

    ```scala 
    import com.ing.baker.types._

    val data: (Type, Value) = (Int32, PrimitiveValue(42))
    ```

=== "Java"

    ```java 
    import com.ing.baker.types.*;

    Type dataType = Int32$.MODULE$;
    Value dataValue = PrimitiveValue.apply(42);
    ```

`Types` are specifically used to describe `Ingredients`, specifically `Ingredients` are just a relation between a name and
a type. 

In a similar way that a programming language variable is just a relation between a name and a type at compile time, the 
baker `Ingredient` is a relation between a name and a Baker `Type` at "recipe time"; the same happens with values, in a 
programming language values must respect types otherwise runtime exceptions are thrown, similarly in Baker, at runtime 
the name of an ingredient will hold a value that respects the ingredient's type.

Here is a complete list of `Types` and `Values` of Baker.

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
