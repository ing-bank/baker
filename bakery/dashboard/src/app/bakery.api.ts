export interface Recipes {
  result: string;
  body:   { [key: string]: RecipeBody };
}

export interface RecipeBody {
  compiledRecipe:    Recipe;
  recipeCreatedTime: number;
  doN:       boolean;
  errors:            string[];
}

export interface Recipe {
  name:              string;
  recipeId:          string;
  recipeCreatedTime: string;
  doNotValidate:       boolean;
  errors:            string[];
}

export interface DigraphResponse {
  result: string;
  body: string;
}

export interface InteractionsResponse {
  result: string;
  body:   Interaction[];
}

export interface EventRecord {
  name: string;
  occurredOn: number;
}

export interface Instance {
  recipeInstanceId: string;
  ingredients:  { [key: string]: JSON };
  events: EventRecord[];
}

export interface InstanceResponse {
  result: string;
  body:   Instance;
}

export interface Interaction {
  id:    string;
  name:  string;
  input: JSON[];
  output?:   { [key: string]: { [key: string]: JSON } };
}
