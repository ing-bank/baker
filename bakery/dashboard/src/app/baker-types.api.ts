// Mirrors com.ing.baker.types.Type
export interface InteractionTypeListTypeInner {
    // eslint-disable-next-line no-use-before-define
    entryType: InteractionType;
}

export interface InteractionTypeOptionTypeInner {
    // eslint-disable-next-line no-use-before-define
    entryType: InteractionType;
}

export interface InteractionTypeEnumTypeInner {
    options: string[];
}

export interface InteractionTypeRecordTypeInner {
    // eslint-disable-next-line no-use-before-define
    fields: RecordField[];
}

export interface InteractionTypeMapTypeInner {
    // eslint-disable-next-line no-use-before-define
    valueType: InteractionType;
}

type PrimitiveName = "Bool" | "Byte" | "Char" | "Int16" | "Int32" | "Int64" |
    "IntBig" | "Float32" | "Float64" | "FloatBig" | "ByteArray" | "CharArray" | "Date"

// for example { "CharArray" : {} }
type InteractionTypePrimitive = Record<PrimitiveName, never>
type InteractionTypeListType = Record<"ListType", InteractionTypeListTypeInner>
type InteractionTypeOptionType = Record<"OptionType", InteractionTypeOptionTypeInner>
type InteractionTypeEnumType = Record<"EnumType", InteractionTypeEnumTypeInner>
type InteractionRecordType = Record<"RecordType", InteractionTypeRecordTypeInner>
type InteractionMapType = Record<"MapType", InteractionTypeMapTypeInner>
type InteractionType =  InteractionTypePrimitive | InteractionTypeListType | InteractionTypeOptionType | InteractionTypeEnumType | InteractionRecordType | InteractionMapType

export interface RecordField {
    name: string;
    type: InteractionType;
}
