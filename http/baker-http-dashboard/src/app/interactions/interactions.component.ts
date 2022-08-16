import {
    Component,
    ElementRef,
    OnInit,
} from "@angular/core";
import {BakerConversionService} from "../baker-conversion.service";
import {BakeryService} from "../bakery.service";
import {Interaction} from "../bakery.api";
import {MatSelectionListChange} from "@angular/material/list";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "interactions",
    "styleUrls": ["interactions.css"],
    "templateUrl": "interactions.component.html"
})
export class InteractionsComponent implements OnInit {
    interactions: Interaction[];
    selectedInteraction: Interaction;
    interactionFilterString: string | undefined;
    filteredInteractions: Interaction[];

    constructor (
        private top: ElementRef,
        private bakeryService: BakeryService,
        private bakerConversionService: BakerConversionService,
    ) {
    }

    ngOnInit (): void {
        this.getInteractions();
    }

    getInteractions (): void {
        this.bakeryService.getInteractions().
            subscribe(interactions => {
                // eslint-disable-next-line id-length
                this.interactions = interactions
                    .map((interaction) => this.bakerConversionService.nameUnnamedIngredients(interaction))
                    .sort((ia, ib) => ia.name.localeCompare(ib.name));
                this.updateInteractionFilter();
            });
    }

    interactionChanged (event: MatSelectionListChange): void {
        this.selectedInteraction = <Interaction>event.options[0].value;
    }

    updateInteractionFilter(): void {
        if (!this.interactionFilterString) {
            this.filteredInteractions = this.interactions;
        } else {
            const filterString = this.interactionFilterString.toLowerCase() || "";
            this.filteredInteractions = this.interactions.filter((interaction) => interaction.name.toLowerCase().includes(filterString) || interaction.id?.toLowerCase()?.includes(filterString));
        }
    }
}

