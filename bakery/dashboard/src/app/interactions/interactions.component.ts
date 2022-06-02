import {
    Component,
    ElementRef,
    OnInit,
    Renderer2,
    ViewChild
} from "@angular/core";
import {BakeryService} from "../bakery.service";
import {Interaction} from "../bakery.api";
import {MatSelectionListChange} from "@angular/material/list";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "dashboard",
    "styleUrls": ["interactions.css"],
    "templateUrl": "interactions.component.html"
})
export class InteractionsComponent implements OnInit {
    interactions: Interaction[];
    selectedInteraction: Interaction;

    selectedInteractionInput (): string {
        return JSON.stringify(this.selectedInteraction?.input, null, 4);
    }

    selectedInteractionOutput (): string {
        return JSON.stringify(this.selectedInteraction?.output, null, 4);
    }

    @ViewChild("interactionView", {"static": false}) interactionView: ElementRef;

    constructor (private top: ElementRef,
        private bakeryService: BakeryService, private renderer: Renderer2) {
    }

    ngOnInit (): void {
        this.getInteractions();
    }

    getInteractions (): void {
        this.bakeryService.getInteractions().
            subscribe(interactions => {
                // eslint-disable-next-line id-length
                this.interactions = interactions.sort((a, b) => a.name.localeCompare(b.name));
            });
    }

    interactionChanged (event: MatSelectionListChange): void {
        this.selectedInteraction = <Interaction>event.options[0].value;
    }
}

