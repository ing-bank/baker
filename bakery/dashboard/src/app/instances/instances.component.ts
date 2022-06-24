import {ActivatedRoute, Router} from "@angular/router";
import {
    Component,
    ElementRef,
    OnInit,
    Renderer2,
    ViewChild
} from "@angular/core";
import {
    EventRecord,
    InstanceIngredientValue,
    InstanceIngredientValueList,
    InstanceIngredientValuePrimitive,
    InstanceIngredientValueRecord,
    InstanceIngredientValueType
} from "../bakery.api";
import {BakeryService} from "../bakery.service";

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
        private renderer: Renderer2,
        private route: ActivatedRoute,
        private router: Router
    ) {
    }
    instanceId: string;
    visual: string | undefined | null;
    instanceEvents: EventRecord[];
    instanceIngredients: InstanceIngredient[];
    displayedInstanceId: string | undefined | null;
    displayedColumns = [
        "eventName",
        "timestamp",
    ];
    failedInstanceId: string | undefined | null;

    @ViewChild("instanceGraph", {"static": false}) instanceGraph: ElementRef;

    ngOnInit (): void {
        if (this.route.snapshot.url.length > 1) {
            this.instanceId = this.route.snapshot.url[1].path;
            this.instanceChanged();
        }
    }

    updateInstance(event: Event): void {
        (event.target as HTMLInputElement)?.blur();
        this.router.navigateByUrl(`/instances/${this.instanceId}`).then(() => this.instanceChanged());
    }

    instanceChanged (): void {
        this.failedInstanceId = null;
        this.loadEventsAndIngredients();
        this.loadGraph();
    }

    loadEventsAndIngredients(): void {
        this.bakeryService.getInstance(this.instanceId).
            // eslint-disable-next-line max-statements
            subscribe(instance => {
                if (instance) {
                    this.displayedInstanceId = instance.recipeInstanceId;
                    // eslint-disable-next-line id-length
                    this.instanceEvents = instance.events.sort((a, b) => a.occurredOn - b.occurredOn);
                    this.instanceIngredients = Object.keys(instance.ingredients)
                        .map((ingredientName) : InstanceIngredient  => ({
                            "isSimple": this.isSimple(instance.ingredients[ingredientName]),
                            "name": ingredientName,
                            "value": JSON.stringify(this.simplifyIngredient(instance.ingredients[ingredientName]), null, 4),
                        }));
                } else {
                    this.failedInstanceId = this.instanceId;
                    this.displayedInstanceId = null;
                    this.instanceEvents = [];
                    this.instanceIngredients = [];
                }
            });
    }

    loadGraph(): void {
        this.bakeryService.getInstanceVisual(this.instanceId).subscribe(visual => {
            this.visual = visual;
        });
    }

    simplifyIngredient(ii : InstanceIngredientValue) : unknown {
        switch (ii.typ) {
        case InstanceIngredientValueType.NullValue: return null;
        case InstanceIngredientValueType.ListValue: return (ii as InstanceIngredientValueList).val.map(this.simplifyIngredient);
        case InstanceIngredientValueType.RecordValue: {
            const record = ii as InstanceIngredientValueRecord;
            // eslint-disable-next-line array-element-newline
            return Object.fromEntries(Object.entries(record.val).map(([name, value]) => [
                name,
                this.simplifyIngredient(value)
            ]));
        }
        case InstanceIngredientValueType.PrimitiveValue: return (ii as InstanceIngredientValuePrimitive).val;
        default: return null;
        }
    }

    isSimple(ii: InstanceIngredientValue) : boolean {
        return ii.typ === InstanceIngredientValueType.NullValue || ii.typ === InstanceIngredientValueType.PrimitiveValue;
    }

    toIsoString(linuxTime: number) : string {
        return new Date(linuxTime).toISOString();
    }
}
