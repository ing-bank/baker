import {
    Component,
    ElementRef,
    OnInit,
    ViewChild
} from "@angular/core";
import {BakeryService} from "../bakery.service";
import {Interaction} from "../bakery.api";
import {MatSelectionListChange} from "@angular/material/list";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "interactions",
    "styleUrls": ["interactions.scss"],
    "templateUrl": "interactions.component.html"
})
export class InteractionsComponent implements OnInit {
    interactions: Interaction[];
    selectedInteraction: Interaction;

    constructor (
        private top: ElementRef,
        private bakeryService: BakeryService
    ) {
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

