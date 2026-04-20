package com.ing.baker.recipe

data class EventOutputTransformer(val newEventName: String, val ingredientRenames: Map<String, String>)