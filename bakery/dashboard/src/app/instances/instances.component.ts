import {ActivatedRoute, Router} from "@angular/router";
import {
    Component,
    ElementRef,
    OnInit,
    Renderer2,
    ViewChild
} from "@angular/core";
import {BakeryService} from "../bakery.service";
import {EventRecord} from "../bakery.api";
import {graphviz} from "d3-graphviz";

@Component({
    "selector": "dashboard",
    "styleUrls": ["instances.css"],
    "templateUrl": "instances.component.html"
})
export class InstancesComponent implements OnInit {
    instanceId: string;

    constructor (
        private top: ElementRef,
        private bakeryService: BakeryService,
        private renderer: Renderer2,
        private route: ActivatedRoute,
        private router: Router
    ) {
    }

    @ViewChild("instanceGraph", {"static": false}) instanceGraph: ElementRef;

    ngOnInit (): void {
        if (this.route.snapshot.url.length > 1) {
            this.loadInstance(this.route.snapshot.url[1].path);
        }
    }

    instanceEvents: EventRecord[];
    instanceIngredients: string[];
    displayedInstanceId: string;

    instanceChanged (): void {
        this.router.navigateByUrl(`/instances/${this.instanceId}`);
    }

    loadInstance (instanceId: string): void {
        this.bakeryService.getInstance(instanceId).
            // eslint-disable-next-line max-statements
            subscribe(instance => {
                const childElements = this.instanceGraph.nativeElement.children;
                for (const child of childElements) {
                    this.renderer.removeChild(this.instanceGraph.nativeElement, child);
                }
                if (instance) {
                    this.displayedInstanceId = instance.recipeInstanceId;
                    // eslint-disable-next-line id-length
                    this.instanceEvents = instance.events.sort((a, b) => a.occurredOn - b.occurredOn);
                    this.instanceIngredients = Object.keys(instance.ingredients);

                    const graph = this.renderer.createElement("div");
                    this.renderer.setAttribute(graph, "id", "graph");
                    this.renderer.appendChild(this.instanceGraph.nativeElement, graph);

                    this.bakeryService.getInstanceVisual(instanceId).
                        subscribe(visual => {
                            graphviz("#graph").
                                renderDot(visual).
                                scale(0.3);
                        });
                }
            });
    }
}
