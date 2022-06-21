import {APP_INITIALIZER, NgModule} from "@angular/core";
import {FormsModule, ReactiveFormsModule} from "@angular/forms";
import {
    MAT_FORM_FIELD_DEFAULT_OPTIONS,
    MatFormFieldModule
} from "@angular/material/form-field";
import {A11yModule} from "@angular/cdk/a11y";
import {BrowserModule} from "@angular/platform-browser";
import {CdkStepperModule} from "@angular/cdk/stepper";
import {CdkTableModule} from "@angular/cdk/table";
import {CdkTreeModule} from "@angular/cdk/tree";
import {ClipboardModule} from "@angular/cdk/clipboard";
import {DragDropModule} from "@angular/cdk/drag-drop";
import {HttpClientModule} from "@angular/common/http";
import {MatButtonModule} from "@angular/material/button";
import {MatButtonToggleModule} from "@angular/material/button-toggle";
import {MatDialogModule} from "@angular/material/dialog";
import {MatGridListModule} from "@angular/material/grid-list";
import {MatIconModule} from "@angular/material/icon";
import {MatInputModule} from "@angular/material/input";
import {MatListModule} from "@angular/material/list";
import {MatSidenavModule} from "@angular/material/sidenav";
import {MatTableModule} from "@angular/material/table";
import {MatToolbarModule} from "@angular/material/toolbar";
import {OverlayModule} from "@angular/cdk/overlay";
import {PortalModule} from "@angular/cdk/portal";
import {ScrollingModule} from "@angular/cdk/scrolling";

// eslint-disable-next-line sort-imports
import {AppComponent} from "./app.component";
import {AppRoutingModule} from "./app-routing.module";
import {AppSettingsService} from "./app.settings";
import {BrowserAnimationsModule} from "@angular/platform-browser/animations";
import {HomeComponent} from "./home/home.component";
import {InstancesComponent} from "./instances/instances.component";
import {InteractionsComponent} from "./interactions/interactions.component";
import {RecipeVisualizeComponent} from "./recipes/visualize/recipe-visualize.component";
import {RecipesComponent} from "./recipes/recipes.component";

// eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
export const initializeApp = (settings: AppSettingsService) => () => settings.load();

@NgModule({
    "bootstrap": [AppComponent],
    "declarations": [
        AppComponent,
        HomeComponent,
        RecipesComponent,
        InteractionsComponent,
        InstancesComponent,
        RecipeVisualizeComponent,
    ],
    "entryComponents": [AppComponent],
    "exports": [
        MatFormFieldModule,
        MatInputModule
    ],
    "imports": [
        BrowserModule,
        BrowserAnimationsModule,
        FormsModule,
        AppRoutingModule,
        HttpClientModule,
        ReactiveFormsModule,
        A11yModule,
        ClipboardModule,
        CdkStepperModule,
        CdkTableModule,
        CdkTreeModule,
        DragDropModule,
        MatButtonModule,
        MatButtonToggleModule,
        MatIconModule,
        MatListModule,
        MatSidenavModule,
        MatToolbarModule,
        OverlayModule,
        PortalModule,
        ScrollingModule,
        MatGridListModule,
        MatFormFieldModule,
        MatInputModule,
        MatDialogModule,
        MatTableModule,
    ],
    "providers": [
        AppSettingsService,
        {
            "deps": [AppSettingsService],
            "multi": true,
            "provide": APP_INITIALIZER,
            "useFactory": initializeApp
        },
        {
            "provide": MAT_FORM_FIELD_DEFAULT_OPTIONS,
            "useValue": {"appearance": "fill"}
        }
    ]
})

export class AppModule {
}
