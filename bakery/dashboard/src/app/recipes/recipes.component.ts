import {Component, ElementRef, OnInit, ViewChild} from "@angular/core";
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
        "recipeName",
        "recipeId",
        "recipeCreatedTime",
        "validate",
        "visualization",
        "errors",
    ];

    @ViewChild("recipeGraph", {"static": true}) recipeGraph: ElementRef;

    constructor(
        private top: ElementRef,
        private bakeryService: BakeryService
    ) {
    }

    ngOnInit(): void {
        this.bakeryService.getRecipes().subscribe(recipes => {
            this.recipes = recipes;
        });
    }
}
