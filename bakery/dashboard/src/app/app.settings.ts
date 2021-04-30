import { Injectable } from '@angular/core';
import {HttpClient} from "@angular/common/http";

const SETTINGS_LOCATION = "assets/settings.json";

export interface AppSettings {
  apiUrl: string;
  title: string;
}

@Injectable()
export class AppSettingsService {
    static settings: AppSettings;
    constructor(private http: HttpClient) {}
    load() {
        return new Promise<void>((resolve, reject) => {
            this.http.get(SETTINGS_LOCATION).toPromise().then(response => {
               AppSettingsService.settings = <AppSettings>response;
               resolve();
            }).catch((response: any) => {
               reject(`Could not load file '${SETTINGS_LOCATION}': ${JSON.stringify(response)}`);
            });
        });
    }
}
