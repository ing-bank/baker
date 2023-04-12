import {
  Component, EventEmitter,
  Input,
  OnChanges,
  OnInit, Output,
} from "@angular/core";
import {
  EventDescriptor,
  ServiceInformation,
  NameAndValue,
  ServiceError, FireEventResponse
} from "../../bakery.api";
import {BakerConversionService} from "../../baker-conversion.service";
import {BakeryService} from "../../bakery.service";
import {Value} from "../../baker-value.api";

type SuccessOrServiceError<A> = {
    "serviceResponse": ServiceInformation<A> | null,
    "serviceError" : ServiceError | null,
    "requestSentAt" : Date,
    "durationInMilliseconds": number,
}

@Component({
    "selector": "instance-manual-test",
    "styleUrls": ["./instance-manual-test.component.scss"],
    "templateUrl": "./instance-manual-test.component.html"
})
export class InstanceManualTestComponent implements OnInit, OnChanges {

    @Input() instanceId: string;
    @Input() selectedEvent: EventDescriptor;

    @Output() reload= new EventEmitter();

    constructor (
        private bakeryService: BakeryService,
        private bakerConversionService: BakerConversionService,
    ) {
    }

    interactionInput: string | undefined;
    interactionIngredientsAsValues: NameAndValue[] | null | undefined;
    executions: SuccessOrServiceError<FireEventResponse>[] = [];
    serviceCallInProgress = false;
    inputErrorMessage: string | undefined | null;

    ngOnInit(): void {
        this.selectedInteractionChanged();
    }

    ngOnChanges() {
        this.selectedInteractionChanged();
    }

    selectedInteractionChanged() : void {
      if(this?.selectedEvent?.ingredients != undefined) {
        this.interactionInput =
          JSON.stringify(this.bakerConversionService.exampleJsonIngredientsList(this.selectedEvent.ingredients), null, 4);
      }
        this.inputElementChanged();
    }

    // eslint-disable-next-line max-statements
    inputElementChanged() : void {
        if (typeof this.interactionInput !== "string") {
            return;
        }
        try {
            const interactionInputJson = JSON.parse(this.interactionInput);
            const valuesOrError = this.bakerConversionService.ingredientsJsonToBakerValues(this.selectedEvent.ingredients, interactionInputJson);
            if (typeof valuesOrError === "string") {
                this.interactionIngredientsAsValues = null;
                this.inputErrorMessage = valuesOrError;
            } else {
                this.interactionIngredientsAsValues = valuesOrError;
                this.inputErrorMessage = null;
            }
        } catch (ex) {
            this.interactionIngredientsAsValues = null;
            this.inputErrorMessage = ex;
        }
    }

    toJson(response : any) : string {
        return JSON.stringify(response, null, 4);
    }

    addLeadingZeros(num: number, totalLength: number): string {
        return String(num).padStart(totalLength, "0");
    }

    toLocalTimestamp(date : Date) : string {
        return `${this.addLeadingZeros(date.getHours(), 2)}:${this.addLeadingZeros(date.getMinutes(), 2)}:${this.addLeadingZeros(date.getSeconds(), 2)}.${this.addLeadingZeros(date.getMilliseconds(), 3)}`;
    }

    toSuccessOrServiceError(response: ServiceInformation<FireEventResponse> | ServiceError) : SuccessOrServiceError<FireEventResponse> {
        if (Object.keys(response).includes("error")) {
            return {
                "serviceResponse": null,
                "serviceError": response as ServiceError,
                "requestSentAt": response.requestSentAt,
                "durationInMilliseconds": response.durationInMilliseconds,
            };
        }
        return {
            "serviceResponse": response as ServiceInformation<FireEventResponse>,
            "serviceError": null,
            "requestSentAt": response.requestSentAt,
            "durationInMilliseconds": response.durationInMilliseconds,
        };
    }

    execute() : void {
        const interactionIngredientsJson = this.interactionIngredientsAsValues;
        if (typeof this.interactionIngredientsAsValues === "undefined" || !interactionIngredientsJson) {
            return;
        }

        this.serviceCallInProgress = true;

        // Map NameAndValue to Record<string, Value>
        const ingredients:Record<string, Value> = interactionIngredientsJson.reduce((acc, cur) => ({...acc, [cur.name]: cur.value}), {})

        this.bakeryService.fireEvent(this.instanceId, this.selectedEvent.name, ingredients).subscribe(executionInformationOrError => {
            this.serviceCallInProgress = false;

            // unshift means prepend.
            this.executions.unshift(this.toSuccessOrServiceError(executionInformationOrError));
            this.reload.emit()
        });
    }

}
