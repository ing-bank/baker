import {Component, ElementRef, OnInit} from "@angular/core";
import {AppSettingsService} from "../app.settings";
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
        "errors",
        "actions",
    ];

    selectedRecipeGraph: string | null;
    selectedRecipeErrors: string[] | null;
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
            this.selectedRecipeErrors = null;
            this.selectedRecipeGraph = visual;
            this.selectedRecipeName = recipeName;
            this.selectedTabIndex = 1;
        });
    }

  viewErrors(recipeId: string, recipeName: string, recipeErrors: string[]): void {
      this.selectedRecipeErrors = recipeErrors;
      this.selectedRecipeGraph = null;
      this.selectedRecipeName = recipeName;
      this.selectedTabIndex = 1;
  }

    bakeRecipe(recipeId: string): void {
        const instanceId = this.randomId(8)
        const baseUrl = (document.querySelector('base') || {}).href;
        this.bakeryService.postBake(instanceId, recipeId).subscribe(() => {
          window.location.href = `${baseUrl}instances/${instanceId}`
        });
    }

    deactivateRecipe(recipeId: string): void {
        this.bakeryService.deactivateRecipe(recipeId).subscribe(() => {
            this.bakeryService.getRecipes().subscribe(recipes => {
                this.recipes = recipes.sort((recipeA, recipeB) => recipeA.recipeCreatedTime - recipeB.recipeCreatedTime).reverse();
            });
        });
    }

    toIsoString(linuxTime: number) : string {
        return new Date(linuxTime).toISOString();
    }

   randomId(length:number) {
    let result = '';
    const characters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    const charactersLength = characters.length;
    let counter = 0;
    while (counter < length) {
      result += characters.charAt(Math.floor(Math.random() * charactersLength));
      counter += 1;
    }
    return result;
  }

}
