import {Component, OnInit, Renderer2} from "@angular/core";
import {AppSettingsService} from "../app.settings";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "dashboard",
    "styleUrls": ["home.css"],
    "templateUrl": "home.component.html"
})
export class HomeComponent implements OnInit {

    bakeryVersion: string;
    stateVersion: string;

    constructor () {
    }

    ngOnInit (): void {
        this.bakeryVersion = AppSettingsService.settings.bakeryVersion;
        this.stateVersion = AppSettingsService.settings.stateVersion;
    }

}
