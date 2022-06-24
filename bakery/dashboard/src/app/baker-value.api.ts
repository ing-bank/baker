// Mirrors com.ing.baker.types.Value
// eslint-disable-next-line no-shadow
export enum ValueType {
    NullValue = 0,
    ListValue = 1,
    RecordValue = 2,
    PrimitiveValue = 3,
}

export type SubType = "java.lang.String" | "java.lang.Character" | "java.math.BigInteger" |
    "java.math.BigDecimal" | "scala.math.BigInt" | "scala.math.BigDecimal"

export type Value =
// eslint-disable-next-line no-use-before-define
    NullValue | ListValue | RecordValue | PrimitiveValue;

export interface NullValue {
    typ: ValueType.NullValue;
}
export interface ListValue {
    typ: ValueType.ListValue;
    val: Value[];
}
export interface RecordValue {
    typ: ValueType.RecordValue;
    val: { [key: string]: Value };
}
export interface PrimitiveValue {
    typ: ValueType.PrimitiveValue;
    styp: SubType;
    val: string | number;
}


