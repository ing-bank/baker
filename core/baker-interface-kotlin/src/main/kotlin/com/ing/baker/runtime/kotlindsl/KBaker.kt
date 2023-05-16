package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.javadsl.Baker
import kotlin.reflect.KVisibility
import kotlin.reflect.full.declaredFunctions

fun main() {
    val bakerClass = Baker::class

    bakerClass.declaredFunctions
        .filter { it.visibility == KVisibility.PUBLIC }
        .map { member -> Pair(member.name, member.returnType.arguments.firstOrNull()?.type ?: member.returnType) }
        .forEach { println("${it.first} - ${it.second}") }
}
