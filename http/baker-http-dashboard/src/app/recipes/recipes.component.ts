import {Component, ElementRef, OnInit} from "@angular/core";
import {BakeryService} from "../bakery.service";
import {Recipe} from "../bakery.api";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "dashboard",
    "styleUrls": ["recipes.scss"],
    "templateUrl": "recipes.component.html",
})
export class RecipesComponent implements OnInit {
    recipes: Recipe[];
    displayedColumns: string[] = [
        "recipeCreatedTime",
        "recipeName",
        "recipeId",
        "validate",
        "visualization",
        "errors",
    ];

    selectedRecipeGraph: string | null;
    selectedRecipeName: string | null;
    selectedTabIndex: number;

    constructor(
        private top: ElementRef,
        private bakeryService: BakeryService
    ) {
    }

    ngOnInit(): void {
        this.bakeryService.getRecipes().subscribe(recipes => {
            this.recipes = recipes.sort((recipeA, recipeB) => recipeA.recipeCreatedTime - recipeB.recipeCreatedTime).reverse();
        });
    }

    viewRecipe(recipeId: string, recipeName: string): void {
        this.bakeryService.getRecipeVisual(recipeId).subscribe(visual => {
            this.selectedRecipeGraph = visual;
            this.selectedRecipeName = recipeName;
            this.selectedTabIndex = 1;
        });
    }

    toIsoString(linuxTime: number) : string {
        return new Date(linuxTime).toISOString();
    }
}
