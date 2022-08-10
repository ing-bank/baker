import {RecordField} from "./baker-types.api";
import {Value} from "./baker-value.api";

export interface Recipe {
  name:              string;
  recipeId:          string;
  recipeCreatedTime: number;
  validate:          boolean;
  errors:            string[];
}

export interface RecipeBodyCompiledRecipe {
  name:             string;
  recipeId:         string;
  validationErrors: string[];
}

export interface RecipeBody {
  compiledRecipe:    RecipeBodyCompiledRecipe;
  recipeCreatedTime: number;
  errors:            string[];
  validate:          boolean;
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

type BakerResultCode = "success" | "error";

export interface InstanceResponse {
  result: BakerResultCode;
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

export interface EventInstance {
  name: string,
  providedIngredients: { [key: string] : Value}
}

export type Option<A> = Record<"value", A> | Record<string, never>
export type Either<L, R> =
    Record<"Left", Record<"value", L>> |
    Record<"Right", Record<"value", R>>

export interface ExecuteInteractionInteractionErrorBody {
  interactionName: string;
  message: string;
}
export type FailureReason =
    Record<"InteractionError", ExecuteInteractionInteractionErrorBody> |
    Record<"NoInstanceFound", never> |
    Record<"Timeout", never> |
    Record<"BadIngredients", never>

export interface InteractionExecutionFailure {
  reason: FailureReason
}

export interface InteractionExecutionSuccess {
  result: EventInstance
}

export interface ExecuteInteractionResponseBody {
  outcome: Either<InteractionExecutionFailure, InteractionExecutionSuccess>;
}

export interface ExecuteInteractionResponse {
  result: BakerResultCode;
  body: ExecuteInteractionResponseBody;
}

export interface SimplifiedFailureReason {
  reason: string;
  interactionErrorMessage: string | null;
}

export interface SimplifiedEventInstance {
  name: string,
  providedIngredients: any;
}

export interface ExecuteInteractionInformation {
  requestSentAt: Date;
  response: ExecuteInteractionResponse;
  durationInMilliseconds : number;
  failureReason: SimplifiedFailureReason | null;
  successEvent: SimplifiedEventInstance | null;
}

export interface ServiceError {
  requestSentAt: Date;
  durationInMilliseconds : number;
  error: any
}
