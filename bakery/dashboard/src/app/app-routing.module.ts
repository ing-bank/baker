import { NgModule } from '@angular/core';
import { RouterModule, Routes } from '@angular/router';

import {RecipesComponent} from './recipes/recipes.component';
import {InteractionsComponent} from "./interactions/interactions.component";
import {InstancesComponent} from "./instances/instances.component";
import {HomeComponent} from "./home/home.component";
import {NotFoundComponent} from "./notfound/notfound.component";

const routes: Routes = [
  { path: '', component: HomeComponent },
  { path: 'recipes', component: RecipesComponent },
  { path: 'recipes/:recipeId', component: RecipesComponent },
  { path: 'interactions', component: InteractionsComponent },
  { path: 'instances', component: InstancesComponent },
  { path: 'instances/:recipeInstanceId', component: InstancesComponent },
  { path: '**', component: NotFoundComponent },
];

@NgModule({
  imports: [ RouterModule.forRoot(routes) ],
  exports: [ RouterModule ]
})
export class AppRoutingModule {}
