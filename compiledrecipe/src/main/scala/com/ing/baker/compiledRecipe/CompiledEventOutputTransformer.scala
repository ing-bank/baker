package com.ing.baker.compiledRecipe


case class CompiledEventOutputTransformer(newEventName: String,
                                          ingredientRenames: Map[String, String])