// Mirrors com.ing.baker.types.Type
export interface TypeListTypeInner {
    // eslint-disable-next-line no-use-before-define
    entryType: Type;
}

export interface TypeOptionTypeInner {
    // eslint-disable-next-line no-use-before-define
    entryType: Type;
}

export interface TypeEnumTypeInner {
    options: string[];
}

export interface TypeRecordTypeInner {
    // eslint-disable-next-line no-use-before-define
    fields: RecordField[];
}

export interface TypeMapTypeInner {
    // eslint-disable-next-line no-use-before-define
    valueType: Type;
}

type PrimitiveTypeName = "Bool" | "Byte" | "Char" | "Int16" | "Int32" | "Int64" |
    "IntBig" | "Float32" | "Float64" | "FloatBig" | "ByteArray" | "CharArray" | "Date"
type NonPrimitiveTypeName = "ListType" | "OptionType" | "EnumType" | "RecordType" | "MapType"
export type TypeName = PrimitiveTypeName | NonPrimitiveTypeName

// for example { "CharArray" : {} }
type TypePrimitive = Record<PrimitiveTypeName, never>
type TypeListType = Record<"ListType", TypeListTypeInner>
type TypeOptionType = Record<"OptionType", TypeOptionTypeInner>
type TypeEnumType = Record<"EnumType", TypeEnumTypeInner>
type RecordType = Record<"RecordType", TypeRecordTypeInner>
type MapType = Record<"MapType", TypeMapTypeInner>
export type Type =  TypePrimitive | TypeListType | TypeOptionType | TypeEnumType | RecordType | MapType

export interface RecordField {
    name: string;
    type: Type;
}
