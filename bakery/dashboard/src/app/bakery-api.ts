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

export interface Interactions {
  result: string;
  body:   Interaction[];
}

export interface Interaction {
  id:    string;
  name:  string;
  input: Input[];
}

export interface Input {
  RecordType?: InputRecordType;
  ListType?:   ListType;
  CharArray?:  CharArrayClass;
}

export interface CharArrayClass {
}

export interface ListType {
  entryType: EntryType;
}

export interface EntryType {
  RecordType: EntryTypeRecordType;
}

export interface EntryTypeRecordType {
  fields: PurpleField[];
}

export interface PurpleField {
  name: string;
  type: PurpleType;
}

export interface PurpleType {
  CharArray: CharArrayClass;
}

export interface InputRecordType {
  fields: FluffyField[];
}

export interface FluffyField {
  name: string;
  type: FluffyType;
}

export interface FluffyType {
  CharArray?:  CharArrayClass;
  ListType?:   ListType;
  ByteArray?:  CharArrayClass;
  RecordType?: EntryTypeRecordType;
}
