import { Injectable } from '@angular/core';
import { HttpClient, HttpHeaders } from '@angular/common/http';

import { Observable, of } from 'rxjs';
import { catchError, map, tap } from 'rxjs/operators';

import {
  Interaction,
  InteractionsResponse,
  Recipe,
  Recipes,
  DigraphResponse,
  InstanceResponse,
  Instance
} from './bakery.api';
import {AppSettingsService} from './app.settings';

@Injectable({ providedIn: 'root' })
export class BakeryService {

  private baseUrl = AppSettingsService.settings.apiUrl;

  httpOptions = {
    headers: new HttpHeaders({ 'Content-Type': 'application/json' })
  };

  constructor(private http: HttpClient) { }

  getRecipes(): Observable<Recipe[]> {
    return this.http.get<Recipes>(this.baseUrl + '/app/recipes')
      .pipe(map(recipes => {
        return Object.values(recipes.body).map(r =>  { const row: Recipe = { name: r.compiledRecipe.name,
                                                       recipeId: r.compiledRecipe.recipeId,
                                                       recipeCreatedTime: new Date(r.recipeCreatedTime).toISOString(),
                                                       validate: r.validate,
                                                       errors: r.compiledRecipe.errors };
                                                        return row;} );
        }));
    };

  getRecipeVisual(recipeId: string): Observable<string> {
    return this.http.get<DigraphResponse>(this.baseUrl + '/app/recipes/' + recipeId + '/visual')
      .pipe(map(response => {
        return response.body;
      }));
  };

  getInteractions(): Observable<Interaction[]> {
    return this.http.get<InteractionsResponse>(this.baseUrl + '/app/interactions')
      .pipe(map(response => {
        return Object.values(response.body);
      }));
  };

  getInstance(instanceId: string): Observable<Instance|undefined> {
    console.log('instance ' + instanceId);
    return this.http.get<InstanceResponse>(this.baseUrl + '/instances/' + instanceId)
      .pipe(
        catchError(this.handleError<InstanceResponse>()),
        map(response => {
          if (response) {
            return response.body;
          } else {
            return undefined;
          }
        }
      ));
  };

  getInstanceVisual(instanceId: string): Observable<string> {
    return this.http.get<DigraphResponse>(this.baseUrl + '/instances/' + instanceId + '/visual')
      .pipe(map(response => {
        return response.body;
      }));
  };

  private handleError<T>(result?: T) {
    return (error: any): Observable<T> => {
      console.log(`http request failed: ${error.message}`);
      return of(result as T);
    };
  }

}
