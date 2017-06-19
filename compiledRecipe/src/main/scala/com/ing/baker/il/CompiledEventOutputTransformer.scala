package com.ing.baker.il


case class CompiledEventOutputTransformer(newEventName: String,
                                          ingredientRenames: Map[String, String])