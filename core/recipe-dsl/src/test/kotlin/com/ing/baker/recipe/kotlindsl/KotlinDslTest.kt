package com.ing.baker.recipe.kotlindsl

import org.jetbrains.annotations.TestOnly
import org.junit.Test
import org.junit.Assert.assertEquals

class KotlinDslTest {
    @Test
    fun `hello test`() {
        assertEquals(KotlinDsl.hello, "World")
    }

    @Test
    fun `false is true`() {
        assertEquals(KotlinDsl.hello, "Hello")
    }
}