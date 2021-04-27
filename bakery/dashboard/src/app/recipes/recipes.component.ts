import {MediaMatcher} from '@angular/cdk/layout';
import {ChangeDetectorRef, Component, OnDestroy, OnInit} from '@angular/core';
import {Recipe} from "../bakery-api";
import {BakeryService} from "../bakery.service";

/** @title Bakery DashboardComponent */
@Component({
  selector: 'dashboard',
  templateUrl: 'recipes.component.html',
  styleUrls: ['recipes.css'],
})
export class RecipesComponent implements OnInit {
  recipes: Recipe[];

  constructor(private bakeryService: BakeryService) { }

  ngOnInit(): void {
    this.getRecipes();
  }

  getRecipes(): void {
    this.bakeryService.getRecipes().subscribe( recipes => this.recipes = recipes);
  }


}
