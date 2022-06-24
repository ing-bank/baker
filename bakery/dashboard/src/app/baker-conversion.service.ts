import {
    ListValue,
    PrimitiveValue,
    RecordValue,
    Value,
    ValueType
} from "./baker-value.api";
import {Injectable} from "@angular/core";

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
}
