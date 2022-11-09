import {HttpClient} from "@angular/common/http";
import {Injectable} from "@angular/core";
import {Value} from "./baker-value.api";

const LOCAL_SETTINGS_LOCATION = "/assets/settings/settings.json";
const SETTINGS_LOCATION = "dashboard_config";

export interface PrefixSettings {
  prefix: string;
}

export interface AppSettings {
  applicationName: string;
  apiPath: string;
  clusterInformation: { [key: string]: string };
}

@Injectable()
export class AppSettingsService {
    static prefix: PrefixSettings;
    static settings: AppSettings;

    constructor (private http: HttpClient) {
    }

    public getAppSettings(prefix: String):Promise<void> {
      return new Promise<void>((resolve, reject) => {
        //For testing purposes:
         AppSettingsService.settings = {
           "applicationName": "Test",
           "apiPath": "/api/bakery",
           "clusterInformation": {"1": "2"}
         };
         resolve()

//         this.http.get(prefix + "/" + SETTINGS_LOCATION).toPromise().then(response => {
//            AppSettingsService.settings = <AppSettings>response;
//            resolve();
//         }).catch((response: any) => {
//             reject(Error(`Could not load file '${SETTINGS_LOCATION}': ${JSON.stringify(response)}`))
//         })
      })
    }

    load () {
      console.log(window.location.href.substring(window.location.href.lastIndexOf('/') + 1));

      AppSettingsService.prefix = {"prefix": window.location.href.substring(window.location.href.lastIndexOf('/') + 1)}
      this.getAppSettings(AppSettingsService.prefix.prefix)
      return new Promise<void>((resolve, reject) => {
            this.getAppSettings(AppSettingsService.prefix.prefix)
              .then(_ => resolve())
      });
    }
}
