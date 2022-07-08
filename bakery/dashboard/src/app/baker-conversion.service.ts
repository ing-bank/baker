import {
    ListValue,
    PrimitiveValue,
    RecordValue,
    SubType,
    Value,
    ValueType
} from "./baker-value.api";
import {
    RecordField,
    Type,
    TypeEnumTypeInner,
    TypeListTypeInner,
    TypeMapTypeInner,
    TypeName,
    TypeOptionTypeInner,
    TypeRecordTypeInner
} from "./baker-types.api";
import {Injectable} from "@angular/core";
import {NameAndValue} from "./bakery.api";

@Injectable({"providedIn": "root"})
export class BakerConversionService {

    valueToJson(ii : Value) : unknown {
        switch (ii.typ) {
        case ValueType.NullValue: return null;
        case ValueType.ListValue: return (ii as ListValue).val.map(this.valueToJson);
        case ValueType.RecordValue: {
            const record = ii as RecordValue;
            // eslint-disable-next-line array-element-newline
            return Object.fromEntries(Object.entries(record.val).map(([name, value]) => [
                name,
                this.valueToJson(value)
            ]));
        }
        case ValueType.PrimitiveValue: return (ii as PrimitiveValue).val;
        default: return null;
        }
    }

    exampleJsonIngredientsList(ingredients: RecordField[]) : unknown {
        return Object.fromEntries(ingredients.map((ingredient) => [
            ingredient.name,
            this.exampleFromType(ingredient.type)
        ]));
    }

    exampleFromType(type : Type) : unknown {
        // eslint-disable-next-line prefer-destructuring
        const [
            typeName,
            typeOptions
        ] = Object.entries(type)[0];

        return this.exampleFromTypeName(typeName as TypeName, typeOptions);
    }

    // eslint-disable-next-line max-lines-per-function
    exampleFromTypeName(typeName : TypeName, options: unknown) : unknown {
        switch (typeName) {
        case "Bool":
            return "false";
        case "Byte":
            return "8";
        case "Char":
            return "B";
        case "Int16":
            return "16";
        case "Int32":
            return "32";
        case "Int64":
            return "64";
        case "IntBig":
            return "128";
        case "Float32":
            return "3.2";
        case "Float64":
            return "6.4";
        case "FloatBig":
            return "12.8";
        case "ByteArray":
            return "ZXhhbXBsZSBieXRlYXJyYXk=";
        case "CharArray":
            return "EXAMPLE VALUE";
        case "ListType":
            return [
                this.exampleFromType((options as TypeListTypeInner).entryType),
                this.exampleFromType((options as TypeListTypeInner).entryType)
            ];
        case "OptionType":
            return this.exampleFromType((options as TypeOptionTypeInner).entryType);
        case "EnumType":
            return (options as TypeEnumTypeInner).options[0];
        case "RecordType": {
            const recordOptions = options as TypeRecordTypeInner;
            return Object.fromEntries(recordOptions.fields.map(recordField => [
                recordField.name,
                this.exampleFromType(recordField.type)
            ]));
        }
        case "MapType": {
            const mapOptions = options as TypeMapTypeInner;
            return Object.fromEntries([
                [
                    "mapKey",
                    this.exampleFromType(mapOptions.valueType)
                ]
            ]);
        }
        default:
            return "Unknown";
        }
    }

    ingredientsJsonToBakerValues(ingredientTypeDefinitions: RecordField[], ingredientsJson: any) : NameAndValue[] | string {
        const resultArray : NameAndValue[] = [];

        for (const typeDefinition of ingredientTypeDefinitions) {
            const value = ingredientsJson[typeDefinition.name];
            if (value === null || typeof (value) === "undefined") {
                return `value for ingredient '${typeDefinition.name}' is missing.`;
            }
            const ingredientValueOrError = this.ingredientValueFromTypeAndJsonValue(typeDefinition.type, value, typeDefinition.name);
            if (typeof ingredientValueOrError === "string") {
                return `incorrect ingredient format for ${ingredientValueOrError}`;
            }
            resultArray.push({
                "name": typeDefinition.name,
                "value": ingredientValueOrError,
            });
        }
        return resultArray;
    }

    ingredientValueFromTypeAndJsonValue(type : Type, value: any, valuePath: string) : Value | string {
        // eslint-disable-next-line prefer-destructuring
        const [
            typeName,
            typeOptions
        ] = Object.entries(type)[0];

        const resultOrError =  this.ingredientValueFromTypeNameAndJsonValue(typeName as TypeName, typeOptions, value, valuePath);
        if (typeof resultOrError === "string") {
            return `${valuePath}: ${resultOrError}`;
        }
        return resultOrError;
    }

    // eslint-disable-next-line max-lines-per-function,complexity
    ingredientValueFromTypeNameAndJsonValue(typeName : TypeName, options: unknown, value: any, valuePath: string) : Value | string {
        if (typeName !== "OptionType" && (value === null || typeof value === "undefined")) {
            return `Expected value at ${valuePath} but was null or undefined.`;
        }

        switch (typeName) {
        case "Bool":
            return this.primitiveValue("java.lang.Boolean", value);
        case "Byte":
            return this.primitiveValue("java.lang.Byte", value);
        case "Char":
            return this.primitiveValue("java.lang.Character", value);
        case "Int16":
            return this.primitiveValue("java.lang.Short", value);
        case "Int32":
            return this.primitiveValue("java.lang.Integer", value);
        case "Int64":
            return this.primitiveValue("java.lang.Long", value);
        case "IntBig":
            return this.primitiveValue("java.math.BigInteger", value);
        case "Float32":
            return this.primitiveValue("java.lang.Float", value);
        case "Float64":
            return this.primitiveValue("java.lang.Double", value);
        case "FloatBig":
            return this.primitiveValue("java.math.BigDecimal", value);
        case "ByteArray":
            return this.primitiveValue("ByteArray", value);
        case "CharArray":
            return this.primitiveValue("java.lang.String", value);
        case "ListType":
            return this.listValue(options as TypeListTypeInner, value, valuePath);
        case "OptionType":
            return this.optionValue(options as TypeOptionTypeInner, value, valuePath);
        case "EnumType": {
            const opts = (options as TypeEnumTypeInner).options;
            if (!opts.includes(value)) {
                return `Expected one of: ${opts}. Was ${value}`;
            }
            return this.primitiveValue("java.lang.String", value);
        }
        case "RecordType":
            return this.recordValue(options as TypeRecordTypeInner, value, valuePath);
        case "MapType":
            return this.mapValue(options as TypeMapTypeInner, value, valuePath);
        default:
            return "Unknown";
        }
    }

    mapValue(mapOptions: TypeMapTypeInner, value: any, valuePath: string): Value | string {
        if (typeof value !== "object" || Array.isArray(value)) {
            return `Expected object at ${value} but wasn't`;
        }
        const valEntries : [string, Value][] = [];

        // eslint-disable-next-line array-element-newline
        for (const [key, val] of Object.entries(value)) {
            const valOrError = this.ingredientValueFromTypeAndJsonValue(mapOptions.valueType, val, `${valuePath}[${key}]`);
            if (typeof valOrError === "string") {
                return valOrError;
            }

            valEntries.push([
                key,
                valOrError
            ]);
        }

        return {
            "typ": ValueType.RecordValue,
            "val": Object.fromEntries(valEntries)
        };
    }

    recordValue(recordOptions: TypeRecordTypeInner, value: any, valuePath: string): Value | string {
        const valEntries : [string, Value][] = [];

        for (const recordField of recordOptions.fields) {
            const valOrError = this.ingredientValueFromTypeAndJsonValue(recordField.type, value[recordField.name], `${valuePath}.${recordField.name}`);

            if (typeof valOrError === "string") {
                return valOrError;
            }

            valEntries.push([
                recordField.name,
                valOrError
            ]);
        }

        return {
            "typ": ValueType.RecordValue,
            "val": Object.fromEntries(valEntries)
        };
    }

    optionValue(optionTypeOptions: TypeOptionTypeInner, value: any | null | undefined, valuePath: string): Value | string {
        if (value === null || typeof (value) === "undefined") {
            return {
                "typ": ValueType.NullValue
            };
        }

        return this.ingredientValueFromTypeAndJsonValue(optionTypeOptions.entryType, value, valuePath);
    }

    listValue(listTypeOptions: TypeListTypeInner, value: any, valuePath: string) : Value | string {
        if (!Array.isArray(value)) {
            return "expected array, but wasn't.";
        }

        const resultVal: Value[] = [];
        // eslint-disable-next-line no-plusplus
        for (let iter = 0; iter < value.length; iter++) {
            const valOrError = this.ingredientValueFromTypeAndJsonValue(listTypeOptions.entryType, value[iter], `${valuePath}[${iter}]`);
            if (typeof valOrError === "string") {
                return valOrError;
            }
            resultVal.push(valOrError);
        }
        return {
            "typ": ValueType.ListValue,
            "val": resultVal,
        };
    }

    primitiveValue(styp: SubType, val: any) : Value | string {
        const valueAsString = `${val}`;
        return {
            styp,
            "typ": ValueType.PrimitiveValue,
            "val": valueAsString,
        };
    }
}
