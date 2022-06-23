import {ActivatedRoute, Router} from "@angular/router";
import {Component, ElementRef, OnInit, Renderer2, ViewChild} from "@angular/core";
import {BakeryService} from "../bakery.service";
import {MatSelectionListChange} from "@angular/material/list";
import {Recipe} from "../bakery.api";
import {graphviz} from "d3-graphviz";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "dashboard",
    "styleUrls": ["recipes.css"],
    "templateUrl": "recipes.component.html",
})
export class RecipesComponent implements OnInit {
    recipes: Recipe[];
    selectedRecipe: Recipe;

    @ViewChild("recipeGraph", {"static": true}) recipeGraph: ElementRef;

    constructor(
        private top: ElementRef,
        private bakeryService: BakeryService,
        private renderer: Renderer2,
        private route: ActivatedRoute,
        private router: Router
    ) {
    }

    ngOnInit(): void {
        this.bakeryService.getRecipes().subscribe(recipes => {
            this.recipes = recipes;
        });
        if (this.route.snapshot.url.length > 1) {
            this.loadRecipe(this.route.snapshot.url[1].path);
        }
    }

    recipeChanged(event: MatSelectionListChange): void {
        const recipe = <Recipe>event.options[0].value;
        this.router.navigateByUrl(`/recipes/${recipe.recipeId}`);
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
