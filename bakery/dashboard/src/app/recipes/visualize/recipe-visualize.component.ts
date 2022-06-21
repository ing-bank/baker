import {ActivatedRoute, Router} from "@angular/router";
import {Component, ElementRef, OnInit, Renderer2, ViewChild} from "@angular/core";
import {BakeryService} from "../../bakery.service";
import {Recipe} from "../../bakery.api";
import {graphviz} from "d3-graphviz";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "dashboard",
    "styleUrls": ["recipe-visualize.scss"],
    "templateUrl": "recipe-visualize.component.html",
})
export class RecipeVisualizeComponent implements OnInit {
    recipes: Recipe[];

    @ViewChild("recipeGraph", {"static": true}) recipeGraph: ElementRef;
    constructor(
        private top: ElementRef,
        private bakeryService: BakeryService,
        private renderer: Renderer2,
        private route: ActivatedRoute,
    ) {
    }

    ngOnInit(): void {
        if (this.route.snapshot.url.length > 1) {
            this.loadRecipe(this.route.snapshot.url[1].path);
        }
    }

    loadRecipe(recipeId: string): void {
        const childElements = this.recipeGraph.nativeElement.children;
        for (const child of childElements) {
            this.renderer.removeChild(this.recipeGraph.nativeElement, child);
        }
        const graph = this.renderer.createElement("div");
        this.renderer.setAttribute(graph, "id", "graph");
        this.renderer.appendChild(this.recipeGraph.nativeElement, graph);

        this.bakeryService.getRecipeVisual(recipeId).subscribe(visual => {
            graphviz("#graph")
                .renderDot(visual)
                .scale(0.3);
        });
    }
}
