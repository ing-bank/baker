import {APP_INITIALIZER, NgModule} from '@angular/core';
import {BrowserModule} from '@angular/platform-browser';
import {FormsModule, ReactiveFormsModule} from '@angular/forms';
import {HttpClientModule} from '@angular/common/http';

import {BrowserAnimationsModule} from "@angular/platform-browser/animations";
import {RecipesComponent} from "./recipes/recipes.component";
import {MAT_FORM_FIELD_DEFAULT_OPTIONS, MatFormFieldModule} from "@angular/material/form-field";
import {A11yModule} from '@angular/cdk/a11y';
import {ClipboardModule} from '@angular/cdk/clipboard';
import {DragDropModule} from '@angular/cdk/drag-drop';
import {PortalModule} from '@angular/cdk/portal';
import {ScrollingModule} from '@angular/cdk/scrolling';
import {CdkStepperModule} from '@angular/cdk/stepper';
import {CdkTableModule} from '@angular/cdk/table';
import {CdkTreeModule} from '@angular/cdk/tree';
import {MatIconModule} from '@angular/material/icon';
import {MatListModule} from '@angular/material/list';
import {MatSidenavModule} from '@angular/material/sidenav';
import {MatToolbarModule} from '@angular/material/toolbar';
import {OverlayModule} from '@angular/cdk/overlay';
import {MatButtonModule} from '@angular/material/button';
import {MatButtonToggleModule} from '@angular/material/button-toggle';
import {AppComponent} from "./app.component";
import {AppRoutingModule} from './app-routing.module';
import {InteractionsComponent} from "./interactions/interactions.component";
import {AppSettingsService} from "./app.settings";
import {MatGridListModule} from "@angular/material/grid-list";
import {InstancesComponent} from "./instances/instances.component";
import {HomeComponent} from "./home/home.component";
import {MatInputModule} from "@angular/material/input";
import {MatDialogModule} from "@angular/material/dialog";

export function initializeApp(settings: AppSettingsService) {
  return () => settings.load();
}

@NgModule({
  imports: [
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
    MatDialogModule
  ],
  entryComponents: [AppComponent],
  declarations: [
    AppComponent,
    HomeComponent,
    RecipesComponent,
    InteractionsComponent,
    InstancesComponent
  ],
   providers: [
         AppSettingsService,
         { provide: APP_INITIALIZER,
           useFactory: initializeApp,
           deps: [AppSettingsService], multi: true },
         {provide: MAT_FORM_FIELD_DEFAULT_OPTIONS, useValue: {appearance: 'fill'}}
   ],
  bootstrap: [AppComponent],
  exports: [ MatFormFieldModule, MatInputModule ]
})

export class AppModule {
}
