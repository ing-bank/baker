import {
    Component,
    ElementRef,
    Input,
    OnInit,
    Renderer2,
    ViewChild
} from "@angular/core";
import {graphviz} from "d3-graphviz";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "visualize-recipe",
    "styleUrls": ["visualize-recipe.scss"],
    "templateUrl": "visualize-recipe.component.html",
})
export class VisualizeRecipeComponent implements OnInit {

    @Input()
    visual : string;

    @ViewChild("recipeGraph", {"static": true}) recipeGraph: ElementRef;
    constructor(
        private top: ElementRef,
        private renderer: Renderer2,
    ) {
    }

    ngOnInit(): void {
        const childElements = this.recipeGraph.nativeElement.children;
        for (const child of childElements) {
            this.renderer.removeChild(this.recipeGraph.nativeElement, child);
        }
        const graph = this.renderer.createElement("div");
        this.renderer.setAttribute(graph, "id", "graph");
        this.renderer.appendChild(this.recipeGraph.nativeElement, graph);

        graphviz("#graph")
            .renderDot(this.visual)
            .scale(0.3);
    }
}
