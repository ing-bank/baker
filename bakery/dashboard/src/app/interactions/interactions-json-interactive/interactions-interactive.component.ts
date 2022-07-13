import {
    Component,
    Input,
    OnChanges,
    OnInit,
} from "@angular/core";
import {ExecuteInteractionInformation, Interaction} from "../../bakery.api";
import {BakerConversionService} from "../../baker-conversion.service";
import {BakeryService} from "../../bakery.service";

@Component({
    "selector": "interactions-interactive",
    "styleUrls": ["./interactions-interactive.component.scss"],
    "templateUrl": "./interactions-interactive.component.html"
})
export class InteractionsInteractiveComponent implements OnInit, OnChanges {

    @Input() selectedInteraction: Interaction;

    constructor (
        private bakeryService: BakeryService,
        private bakerConversionService: BakerConversionService,
    ) {
    }

    interactionInput: string | undefined;
    interactionIngredientsAsValues: any | undefined;
    executions: ExecuteInteractionInformation[] = [];
    executeButtonDisabled = false;

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

    inputElementChanged() : void {
        if (typeof this.interactionInput !== "string") {
            return;
        }
        const interactionInputJson = JSON.parse(this.interactionInput);
        this.interactionIngredientsAsValues = this.bakerConversionService.ingredientsJsonToBakerValues(this.selectedInteraction.input, interactionInputJson);
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

    execute() : void {
        if (typeof this.interactionIngredientsAsValues === "undefined") {
            return;
        }

        const interactionIngredientsJson = this.interactionIngredientsAsValues;
        this.executeButtonDisabled = true;

        this.bakeryService.executeInteraction(this.selectedInteraction.id, interactionIngredientsJson).subscribe(executionInformation => {
            // unshift means prepend.
            this.executions.unshift(executionInformation);
            this.executeButtonDisabled = false;
        });
    }

}
