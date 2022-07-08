import {
    DigraphResponse, ExecuteInteractionRequest,
    Instance,
    InstanceResponse,
    Interaction,
    InteractionsResponse, NameAndValue,
    Recipe,
    Recipes
} from "./bakery.api";
import {HttpClient, HttpHeaders} from "@angular/common/http";

import {Observable, of} from "rxjs";
import {catchError, map} from "rxjs/operators";
import {AppSettingsService} from "./app.settings";

import {Injectable} from "@angular/core";

@Injectable({"providedIn": "root"})
export class BakeryService {

    private baseUrl = AppSettingsService.settings.apiUrl;

    httpOptions = {
        "headers": new HttpHeaders({"Content-Type": "application/json"})
    };

    constructor (private http: HttpClient) {
    }

    getRecipes (): Observable<Recipe[]> {
        return this.http.get<Recipes>(`${this.baseUrl}/app/recipes`).
            pipe(map(recipes => Object.values(recipes.body)
                .map(response => {
                    const row: Recipe = {
                        "errors": response.compiledRecipe.errors,
                        "name": response.compiledRecipe.name,
                        "recipeCreatedTime": response.recipeCreatedTime,
                        "recipeId": response.compiledRecipe.recipeId,
                        "validate": response.validate
                    };
                    return row;
                })));
    }

    getRecipeVisual (recipeId: string): Observable<string> {
        return this.http.get<DigraphResponse>(`${this.baseUrl}/app/recipes/${recipeId}/visual`).
            pipe(map(response => response.body));
    }

    getInteractions (): Observable<Interaction[]> {
        return this.http.get<InteractionsResponse>(`${this.baseUrl}/app/interactions`).
            pipe(map(response => Object.values(response.body)));
    }

    getInstance (instanceId: string): Observable<Instance | null> {
        return this.http.get<InstanceResponse>(`${this.baseUrl}/instances/${instanceId}`).
            pipe(
                catchError(this.handleError<InstanceResponse>(null)),
                map(response => {
                    if (response && response.result === "success") {
                        return response.body;
                    }
                    return null;
                })
            );
    }

    getInstanceVisual (instanceId: string): Observable<string | null> {
        return this.http.get<DigraphResponse>(`${this.baseUrl}/instances/${instanceId}/visual`).
            pipe(
                catchError(this.handleError<DigraphResponse>(null)),
                map(response => {
                    if (response && response.result === "success") {
                        return response.body;
                    }
                    return null;
                })
            );
    }

    executeInteraction(interactionId: string, ingredients: NameAndValue[]): Observable<any> {
        const request : ExecuteInteractionRequest = {
            "id": interactionId,
            ingredients
        };

        return this.http.post<any>(`${this.baseUrl}/app/interactions/execute`, request);
    }

    private handleError<T> (result: T | null) {
        return (error: any): Observable<T> => {
            // eslint-disable-next-line no-console
            console.log(`http request failed: ${error.message}`);
            return of(result as T);
        };
    }

}
