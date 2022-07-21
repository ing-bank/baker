import {Component, Input, OnInit} from "@angular/core";
import {Interaction} from "../../bakery.api";

@Component({
    "selector": "interaction-definition",
    "styleUrls": ["./interaction-definition.component.scss"],
    "templateUrl": "./interaction-definition.component.html"
})
export class InteractionDefinitionComponent implements OnInit {

    @Input() selectedInteraction: Interaction;

    ngOnInit(): void {
    }

    selectedInteractionInput (): string {
        return JSON.stringify(this.selectedInteraction?.input, null, 4);
    }

    selectedInteractionOutput (): string {
        return JSON.stringify(this.selectedInteraction?.output, null, 4);
    }

}
