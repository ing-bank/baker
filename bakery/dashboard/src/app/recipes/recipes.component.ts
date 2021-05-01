import {Component, EventEmitter, Input, OnChanges, OnInit, Output, SimpleChanges} from '@angular/core';
import {Recipe} from "../bakery.api";
import {BakeryService} from "../bakery.service";
import {graphviz}  from 'd3-graphviz';
import {MatSelectionListChange} from "@angular/material/list";

/** @title Bakery DashboardComponent */
@Component({
  selector: 'dashboard',
  templateUrl: 'recipes.component.html',
  styleUrls: ['recipes.css'],
})
export class RecipesComponent implements OnInit {
  recipes: Recipe[];
  selectedRecipe: Recipe;

  constructor(private bakeryService: BakeryService) { }

  ngOnInit(): void {
    this.bakeryService.getRecipes().subscribe( recipes => this.recipes = recipes);
  }

  recipeChanged(event: MatSelectionListChange): void {
    let recipe = <Recipe> event.options[0].value;
    this.bakeryService.getRecipeVisual(recipe.recipeId).subscribe(v =>
      { graphviz('#recipeGraph').renderDot(v).scale(0.3); }
    );
  }
}
