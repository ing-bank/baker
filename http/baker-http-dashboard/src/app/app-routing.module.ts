import {RouterModule, Routes} from "@angular/router";
import {HomeComponent} from "./home/home.component";
import {InstancesComponent} from "./instances/instances.component";
import {InteractionsComponent} from "./interactions/interactions.component";
import {NgModule} from "@angular/core";
import {NotFoundComponent} from "./notfound/notfound.component";
import {AppSettingsService} from "./app.settings";

import {RecipesComponent} from "./recipes/recipes.component";

const routes: Routes = [
    {
        "component": HomeComponent,
        "path": ""
    },
    {
        "component": RecipesComponent,
        "path": "recipes"
    },
    {
        "component": InteractionsComponent,
        "path": "interactions",
    },
    {
        "component": InstancesComponent,
        "path": "instances",
    },
    {
        "component": InstancesComponent,
        "path": "instances/:recipeInstanceId",
    },
    {
        "component": HomeComponent,
        "path": ":prefix"
    },
    {
        "component": RecipesComponent,
        "path": ":prefix/recipes"
    },
    {
        "component": InteractionsComponent,
        "path": ":prefix/interactions",
    },
    {
        "component": InstancesComponent,
        "path": ":prefix/instances",
    },
    {
        "component": InstancesComponent,
        "path": ":prefix/instances/:recipeInstanceId",
    },
    {
        "component": NotFoundComponent,
        "path": "**",
    }
];

@NgModule({
    "exports": [RouterModule],
    "imports": [RouterModule.forRoot(routes)],
})
export class AppRoutingModule {
}
