package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.inmemory.InMemoryBaker
import com.ing.baker.runtime.model.BakerConfig

object InMemoryBaker {
    fun kotlin(implementations: List<Any> = emptyList()) = Baker(InMemoryBaker.java(implementations))

    /**
     * Creates a InMemoryBaker with the com.ing.baker.runtime.kotlindsl.InMemoryBaker.Config.
     */
    fun kotlin(config: BakerConfig,
               implementations: List<Any> = emptyList()) = Baker(InMemoryBaker.java(config, implementations))

}
