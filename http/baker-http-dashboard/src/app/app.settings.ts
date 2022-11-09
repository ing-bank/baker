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
      const url = new URL(window.location.href);

      // if there is an empty path or just a / the prefix is empty
      if(url.pathname == "/" || url.pathname.length == 0) {
        AppSettingsService.prefix = {"prefix": url.pathname.substring(url.pathname.lastIndexOf('/') + 1)}
      }
      // If there is a path we need to ensure they are not part of the path
      else {
        var temp = url.pathname;
        if(temp.includes('/recipes')) {
          temp = temp.substring(0, temp.lastIndexOf('/recipes'))
        }
        if(temp.includes('/interactions')) {
            temp = temp.substring(0, temp.lastIndexOf('/interactions'))
        }
        if(temp.includes('/instances')) {
            temp = temp.substring(0, temp.lastIndexOf('/instances'))
        }
        if(temp.lastIndexOf("/") > 0) {
          temp = temp.substring(0, temp.lastIndexOf('/'))
        }
        console.log("temp:" + temp)
        AppSettingsService.prefix = {"prefix": temp}
      }

      return new Promise<void>((resolve, reject) => {
            this.getAppSettings(AppSettingsService.prefix.prefix)
              .then(_ => resolve())
      });
    }
}
