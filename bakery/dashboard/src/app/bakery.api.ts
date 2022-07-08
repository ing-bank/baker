import {RecordField} from "./baker-types.api";
import {Value} from "./baker-value.api";

export interface Recipe {
  name:              string;
  recipeId:          string;
  recipeCreatedTime: number;
  validate:          boolean;
  errors:            string[];
}

export interface RecipeBody {
  compiledRecipe:    Recipe;
  recipeCreatedTime: number;
  validate:          boolean;
  errors:            string[];
}

export interface Recipes {
  result: string;
  body:   { [key: string]: RecipeBody };
}

export interface DigraphResponse {
  result: string;
  body: string;
}

export interface Interaction {
  id:    string;
  name:  string;
  input: RecordField[];
  output?:   { [eventName: string]: RecordField };
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
  ingredients:  { [key: string]: Value };
  events: EventRecord[];
}

export interface InstanceResponse {
  result: "success" | "error";
  body:   Instance;
}


export interface NameAndValue {
  name: string;
  value: Value;
}

export interface ExecuteInteractionRequest {
  id: string;
  ingredients: NameAndValue[];
}


