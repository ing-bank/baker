import {Component, OnInit} from "@angular/core";
import {AppSettingsService} from "../app.settings";

/** @title Bakery DashboardComponent */
@Component({
    "selector": "dashboard",
    "styleUrls": ["home.css"],
    "templateUrl": "home.component.html"
})
export class HomeComponent implements OnInit {

    clusterInformation: string;

    constructor () {
    }

    ngOnInit (): void {
        this.clusterInformation = JSON.stringify(AppSettingsService.settings.clusterInformation);
    }

}
