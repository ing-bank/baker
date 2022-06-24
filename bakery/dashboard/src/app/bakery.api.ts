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
  input: JSON[];
  output?:   { [key: string]: { [key: string]: JSON } };
}


export interface InteractionsResponse {
  result: string;
  body:   Interaction[];
}

export interface EventRecord {
  name: string;
  occurredOn: number;
}

// eslint-disable-next-line no-shadow
export enum InstanceIngredientValueType {
  NullValue = 0,
  ListValue = 1,
  RecordValue = 2,
  PrimitiveValue = 3,
}

export type InstanceIngredientValue =
// eslint-disable-next-line no-use-before-define
    InstanceIngredientValueNull | InstanceIngredientValueList | InstanceIngredientValueRecord | InstanceIngredientValuePrimitive;

export interface InstanceIngredientValueNull {
  typ: InstanceIngredientValueType.NullValue;
}
export interface InstanceIngredientValueList {
  typ: InstanceIngredientValueType.ListValue;
  val: InstanceIngredientValue[];
}
export interface InstanceIngredientValueRecord {
  typ: InstanceIngredientValueType.RecordValue;
  val: { [key: string]: InstanceIngredientValue };
}
export interface InstanceIngredientValuePrimitive {
  typ: InstanceIngredientValueType.PrimitiveValue;
  styp: string;
  val: string | number;
}

export interface Instance {
  recipeInstanceId: string;
  ingredients:  { [key: string]: InstanceIngredientValue };
  events: EventRecord[];
}

export interface InstanceResponse {
  result: "success" | "error";
  body:   Instance;
}

