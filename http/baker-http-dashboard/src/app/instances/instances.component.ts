import {ActivatedRoute, Router} from "@angular/router";
import {
    Component,
    ElementRef,
    OnInit,
    Renderer2,
    ViewChild
} from "@angular/core";
import {Value, ValueType} from "../baker-value.api";
import {BakerConversionService} from "../baker-conversion.service";
import {BakeryService} from "../bakery.service";
import {EventDescriptor, EventRecord, Interaction} from "../bakery.api";
import {AppSettingsService} from "../app.settings";
import {MatSelectionListChange} from "@angular/material/list";

type InstanceIngredient = { name : string, value: string, isSimple: boolean };

@Component({
    "selector": "dashboard",
    "styleUrls": ["instances.css"],
    "templateUrl": "instances.component.html"
})
export class InstancesComponent implements OnInit {
    constructor (
        private top: ElementRef,
        private bakeryService: BakeryService,
        private bakerConversionService: BakerConversionService,
        private renderer: Renderer2,
        private route: ActivatedRoute,
        private router: Router
    ) {
    }
    instanceId: string;
    visual: string | undefined | null;

    events: EventDescriptor[];
    selectedEvent: EventDescriptor;

    instanceEvents: EventRecord[];
    instanceIngredients: InstanceIngredient[];
    displayedInstanceId: string | undefined | null;
    displayedColumns = [
        "eventName",
        "timestamp",
    ];
    failedInstanceId: string | undefined | null;

    selectedInteraction: Interaction

    @ViewChild("instanceGraph", {"static": false}) instanceGraph: ElementRef;

    ngOnInit (): void {
        let lastUrl = this.route.snapshot.url[this.route.snapshot.url.length-1].path
        if (lastUrl != "instances") {
            this.instanceId = lastUrl
            this.instanceChanged();
        }
    }

    updateInstance(event: Event): void {
        (event.target as HTMLInputElement)?.blur();
        this.router.navigateByUrl(AppSettingsService.prefix.prefix + `/instances/${this.instanceId}`).then(() => this.instanceChanged());
    }

    instanceChanged (): void {
        this.failedInstanceId = null;
        this.loadEventsAndIngredients();
        this.loadGraph();
    }

    eventChanged (event: MatSelectionListChange):void{
      this.selectedEvent = <EventDescriptor>event.options[0].value;
    }

    loadEventsAndIngredients(): void {
        this.bakeryService.getInstance(this.instanceId).
            // eslint-disable-next-line max-statements
            subscribe(instance => {
                if (instance) {
                    this.loadRecipe(instance.recipeId)
                    this.displayedInstanceId = instance.recipeInstanceId;
                    // eslint-disable-next-line id-length
                    this.instanceEvents = instance.events.sort((a, b) => a.occurredOn - b.occurredOn);
                    this.instanceIngredients = Object.keys(instance.ingredients)
                        .map((ingredientName) : InstanceIngredient  => ({
                            "isSimple": this.isSimple(instance.ingredients[ingredientName]),
                            "name": ingredientName,
                            "value": JSON.stringify(this.bakerConversionService.valueToJson(instance.ingredients[ingredientName]), null, 4),
                        }));
                } else {
                    this.failedInstanceId = this.instanceId;
                    this.displayedInstanceId = null;
                    this.instanceEvents = [];
                    this.instanceIngredients = [];
                }
            });
    }

    loadRecipe(recipeId: string): void {
      this.bakeryService.getRecipe(recipeId).
        // eslint-disable-next-line max-statements
        subscribe(recipe => {
          this.events = recipe.sensoryEvents
        });
    }

    loadGraph(): void {
        this.bakeryService.getInstanceVisual(this.instanceId).subscribe(visual => {
            this.visual = visual;
        });
    }

    isSimple(ii: Value) : boolean {
        return ii.typ === ValueType.NullValue || ii.typ === ValueType.PrimitiveValue;
    }

    toIsoString(linuxTime: number) : string {
        return new Date(linuxTime).toISOString();
    }
}
