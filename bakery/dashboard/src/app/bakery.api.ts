export interface Recipes {
  result: string;
  body:   { [key: string]: RecipeBody };
}

export interface RecipeBody {
  compiledRecipe:    Recipe;
  recipeCreatedTime: number;
  errors:            string[];
}

export interface Recipe {
  name:             string;
  recipeId:         string;
  validationErrors: string[];
}

export interface RecipeVisual {
  result: string;
  body: string;
}

export interface Interactions {
  result: string;
  body:   Interaction[];
}

export interface Interaction {
  id:    string;
  name:  string;
  input: JSON[];
  output?:   { [key: string]: { [key: string]: JSON } };
}
