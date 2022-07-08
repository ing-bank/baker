import {
    Component,
    Input,
    OnChanges,
    OnInit,
    SimpleChanges
} from "@angular/core";
import {BakerConversionService} from "../../baker-conversion.service";
import {BakeryService} from "../../bakery.service";
import {Interaction} from "../../bakery.api";

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
    interactionExecutionOutput: string | undefined;

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

    execute() : void {
        if (typeof this.interactionIngredientsAsValues === "undefined") {
            return;
        }

        const interactionIngredientsJson = this.interactionIngredientsAsValues;

        this.bakeryService.executeInteraction(this.selectedInteraction.id, interactionIngredientsJson).subscribe(response => {
            this.interactionExecutionOutput = JSON.stringify(response, null, 4);
        });
    }

}
