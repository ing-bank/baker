import { Injectable } from '@angular/core';
import { HttpClient, HttpHeaders } from '@angular/common/http';

import { Observable, of } from 'rxjs';
import { catchError, map, tap } from 'rxjs/operators';

import {Interaction, Interactions, Recipe, Recipes, RecipeVisual} from './bakery.api';
import {AppSettingsService} from './app.settings';

@Injectable({ providedIn: 'root' })
export class BakeryService {

  private baseUrl = AppSettingsService.settings.apiUrl;

  httpOptions = {
    headers: new HttpHeaders({ 'Content-Type': 'application/json' })
  };

  constructor(

    private http: HttpClient) { }

  getRecipes(): Observable<Recipe[]> {
    return this.http.get<Recipes>(this.baseUrl + '/app/recipes')
      .pipe(map(recipes => {
        return Object.values(recipes.body).map(r => r.compiledRecipe);
      }));
      // .pipe(catchError(this.handleError<Recipes>('getRecipes')));
    };

  getRecipeVisual(recipeId: string): Observable<string> {
    return this.http.get<RecipeVisual>(this.baseUrl + '/app/recipes/' + recipeId + '/visual')
      .pipe(map(recipeVisual => {
        return recipeVisual.body;
      }));
    // .pipe(catchError(this.handleError<Recipes>('getRecipes')));
  };

  getInteractions(): Observable<Interaction[]> {
    return this.http.get<Interactions>(this.baseUrl + '/app/interactions')
      .pipe(map(interactions => {
        return Object.values(interactions.body);
      }));
    // .pipe(catchError(this.handleError<Recipes>('getRecipes')));
  };

  /**
   * Handle Http operation that failed.
   * Let the app continue.
   * @param operation - name of the operation that failed
   * @param result - optional value to return as the observable result
   */
  private handleError<T>(operation = 'operation', result?: T) {
    return (error: any): Observable<T> => {

      // TODO: send the error to remote logging infrastructure
      console.error(error); // log to console instead

      // TODO: better job of transforming error for user consumption
      this.log(`${operation} failed: ${error.message}`);

      // Let the app keep running by returning an empty result.
      return of(result as T);
    };
  }

  /** Log a BakeryService message with the MessageService */
  private log(message: string) {
    console.log(`BakeryService: ${message}`);
  }
}
