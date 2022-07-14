import {Interaction, NameAndValue} from "./bakery.api";
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
    TypeOptionTypeInner,
    TypeRecordTypeInner
} from "./baker-types.api";
import {Injectable} from "@angular/core";

@Injectable({"providedIn": "root"})
export class BakerConversionService {

    /**
     * ===========================================
     * Simplify baker value to simple json format.
     * ===========================================
     */
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

    /**
     * ===========================================
     * Create example ingredients map
     * input: from type information (from /app/interactions endpoint),
     * output: example ingredients in simple json format.
     * ===========================================
     */
    exampleJsonIngredientsList(ingredients: RecordField[]) : unknown {
        return Object.fromEntries(ingredients.map((ingredient) => [
            ingredient.name,
            this.exampleFromType(ingredient.type)
        ]));
    }

    // eslint-disable-next-line max-lines-per-function
    private exampleFromType(type : Type) : unknown {
        // eslint-disable-next-line prefer-destructuring
        const [
            typeName,
            typeOptions
        ] = Object.entries(type)[0];

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
                this.exampleFromType((typeOptions as TypeListTypeInner).entryType),
                this.exampleFromType((typeOptions as TypeListTypeInner).entryType)
            ];
        case "OptionType":
            return this.exampleFromType((typeOptions as TypeOptionTypeInner).entryType);
        case "EnumType":
            return (typeOptions as TypeEnumTypeInner).options[0];
        case "RecordType": {
            const recordOptions = typeOptions as TypeRecordTypeInner;
            return Object.fromEntries(recordOptions.fields.map(recordField => [
                recordField.name,
                this.exampleFromType(recordField.type)
            ]));
        }
        case "MapType": {
            const mapOptions = typeOptions as TypeMapTypeInner;
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

    /**
     * ===========================================
     * Create baker Value objects by combining information from:
     * 1. Ingredient type definitions (from /app/interactions endpoint)
     * 2. Simplified json containing the actual values.
     * ===========================================
     * @returns a list of name/value pairs OR an error message.
     */
    ingredientsJsonToBakerValues(ingredientTypeDefinitions: RecordField[], ingredientsJson: any) : NameAndValue[] | string {
        const resultArray : NameAndValue[] = [];

        // Loop over the ingredients for this interaction.
        for (const typeDefinition of ingredientTypeDefinitions) {
            const value = ingredientsJson[typeDefinition.name];
            if (value === null || typeof (value) === "undefined") {
                return `value for ingredient '${typeDefinition.name}' is missing.`;
            }
            const ingredientValueOrError = this.ingredientValueFromTypeAndJsonValue(typeDefinition.type, value, typeDefinition.name);
            // If parsing an underlying value failed, return that error.
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

    // eslint-disable-next-line max-lines-per-function,complexity
    private ingredientValueFromTypeAndJsonValue(type : Type, value: any, valuePath: string) : Value | string {
        // eslint-disable-next-line prefer-destructuring
        const [
            typeName,
            typeOptions
        ] = Object.entries(type)[0];

        if (typeName !== "OptionType" && (value === null || typeof value === "undefined")) {
            return `Expected value at ${valuePath} but was null or undefined.`;
        }

        switch (typeName) {
        case "Bool":
            return BakerConversionService.primitiveValue("java.lang.Boolean", value);
        case "Byte":
            return BakerConversionService.primitiveValue("java.lang.Byte", value);
        case "Char":
            return BakerConversionService.primitiveValue("java.lang.Character", value);
        case "Int16":
            return BakerConversionService.primitiveValue("java.lang.Short", value);
        case "Int32":
            return BakerConversionService.primitiveValue("java.lang.Integer", value);
        case "Int64":
            return BakerConversionService.primitiveValue("java.lang.Long", value);
        case "IntBig":
            return BakerConversionService.primitiveValue("java.math.BigInteger", value);
        case "Float32":
            return BakerConversionService.primitiveValue("java.lang.Float", value);
        case "Float64":
            return BakerConversionService.primitiveValue("java.lang.Double", value);
        case "FloatBig":
            return BakerConversionService.primitiveValue("java.math.BigDecimal", value);
        case "ByteArray":
            return BakerConversionService.primitiveValue("ByteArray", value);
        case "CharArray":
            return BakerConversionService.primitiveValue("java.lang.String", value);
        case "ListType":
            return this.listValue(typeOptions as TypeListTypeInner, value, valuePath);
        case "OptionType":
            return this.optionValue(typeOptions as TypeOptionTypeInner, value, valuePath);
        case "EnumType": {
            const opts = (typeOptions as TypeEnumTypeInner).options;
            if (!opts.includes(value)) {
                return `Expected one of: ${opts}. Was ${value}`;
            }
            return BakerConversionService.primitiveValue("java.lang.String", value);
        }
        case "RecordType":
            return this.recordValue(typeOptions as TypeRecordTypeInner, value, valuePath);
        case "MapType":
            return this.mapValue(typeOptions as TypeMapTypeInner, value, valuePath);
        default:
            return "Unknown";
        }
    }

    private mapValue(mapOptions: TypeMapTypeInner, value: any, valuePath: string): Value | string {
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

    private recordValue(recordOptions: TypeRecordTypeInner, value: any, valuePath: string): Value | string {
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

    private optionValue(optionTypeOptions: TypeOptionTypeInner, value: any | null | undefined, valuePath: string): Value | string {
        if (value === null || typeof (value) === "undefined") {
            return {
                "typ": ValueType.NullValue
            };
        }

        return this.ingredientValueFromTypeAndJsonValue(optionTypeOptions.entryType, value, valuePath);
    }

    private listValue(listTypeOptions: TypeListTypeInner, value: any, valuePath: string) : Value | string {
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

    private static primitiveValue(styp: SubType, val: any) : Value | string {
        const valueAsString = `${val}`;
        return {
            styp,
            "typ": ValueType.PrimitiveValue,
            "val": valueAsString,
        };
    }

    nameUnnamedIngredients(interaction: Interaction) : Interaction {
        let unnamedFieldNumber = 0;

        return {
            "id": interaction.id,
            "name": interaction.name,
            "input": interaction.input.map((input: RecordField) => {
                // eslint-disable-next-line no-plusplus
                const name = input.name || `Unnamed field ${++unnamedFieldNumber}`;
                return {
                    name,
                    "type": input.type
                };
            }),
            "output": interaction.output
        };
    }
}
