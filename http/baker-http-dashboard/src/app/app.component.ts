import {ChangeDetectorRef, Component, OnDestroy, OnInit} from "@angular/core";
import {AppSettingsService} from "./app.settings";
import {MediaMatcher} from "@angular/cdk/layout";
import {wasmFolder} from "@hpcc-js/wasm";

@Component({
    "selector": "app",
    "styleUrls": ["./app.component.css"],
    "templateUrl": "./app.component.html"
})
export class AppComponent implements OnDestroy, OnInit {
    title = AppSettingsService.settings.applicationName;
    mobileQuery: MediaQueryList;

    private readonly mobileQueryListener: () => void;

    constructor (changeDetectorRef: ChangeDetectorRef, media: MediaMatcher) {
        this.mobileQuery = media.matchMedia("(max-width: 600px)");
        this.mobileQueryListener = () => changeDetectorRef.detectChanges();
        this.mobileQuery.addListener(this.mobileQueryListener);
    }


    ngOnDestroy (): void {
        this.mobileQuery.removeListener(this.mobileQueryListener);
    }

    ngOnInit (): void {
        wasmFolder("/assets/@hpcc-js/wasm/dist/");
    }
}
