package com.ing.baker.recipe

data class CheckPointEvent(
    val name: String = "",
    val requiredEvents: Set<String> = emptySet(),
    val requiredOneOfEvents: Set<Set<String>> = emptySet(),
)

