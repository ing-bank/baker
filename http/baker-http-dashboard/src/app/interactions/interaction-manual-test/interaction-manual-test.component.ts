import {
    Component,
    Input,
    OnChanges,
    OnInit,
} from "@angular/core";
import {
    ExecuteInteractionInformation,
    Interaction, NameAndValue,
    ServiceError
} from "../../bakery.api";
import {BakerConversionService} from "../../baker-conversion.service";
import {BakeryService} from "../../bakery.service";

type SuccessOrServiceError = {
    "serviceResponse": ExecuteInteractionInformation | null,
    "serviceError" : ServiceError | null,
    "requestSentAt" : Date,
    "durationInMilliseconds": number,
}

@Component({
    "selector": "interaction-manual-test",
    "styleUrls": ["./interaction-manual-test.component.scss"],
    "templateUrl": "./interaction-manual-test.component.html"
})
export class InteractionManualTestComponent implements OnInit, OnChanges {

    @Input() selectedInteraction: Interaction;

    constructor (
        private bakeryService: BakeryService,
        private bakerConversionService: BakerConversionService,
    ) {
    }

    interactionInput: string | undefined;
    interactionIngredientsAsValues: NameAndValue[] | null | undefined;
    executions: SuccessOrServiceError[] = [];
    serviceCallInProgress = false;
    inputErrorMessage: string | undefined | null;

    ngOnInit(): void {
        this.selectedInteractionChanged();
    }

    ngOnChanges() {
        this.selectedInteractionChanged();
    }

    selectedInteractionChanged() : void {
        this.interactionInput =
            JSON.stringify(this.bakerConversionService.exampleJsonIngredientsList(this.selectedInteraction?.input), null, 4);

        this.inputElementChanged();
    }

    // eslint-disable-next-line max-statements
    inputElementChanged() : void {
        if (typeof this.interactionInput !== "string") {
            return;
        }
        try {
            const interactionInputJson = JSON.parse(this.interactionInput);
            const valuesOrError = this.bakerConversionService.ingredientsJsonToBakerValues(this.selectedInteraction.input, interactionInputJson);
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

    toSuccessOrServiceError(response: ExecuteInteractionInformation | ServiceError) : SuccessOrServiceError {
        if (Object.keys(response).includes("error")) {
            return {
                "serviceResponse": null,
                "serviceError": response as ServiceError,
                "requestSentAt": response.requestSentAt,
                "durationInMilliseconds": response.durationInMilliseconds,
            };
        }
        return {
            "serviceResponse": response as ExecuteInteractionInformation,
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

        this.bakeryService.executeInteraction(this.selectedInteraction.id, interactionIngredientsJson).subscribe(executionInformationOrError => {
            this.serviceCallInProgress = false;

            // unshift means prepend.
            this.executions.unshift(this.toSuccessOrServiceError(executionInformationOrError));
        });
    }

}
