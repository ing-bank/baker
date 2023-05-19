package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.inmemory.InMemoryBaker
import com.ing.baker.runtime.model.BakerF

object InMemoryBaker {
    fun kotlin(implementations: List<Any> = emptyList()) = Baker(InMemoryBaker.java(implementations))

    fun kotlin(config: BakerF.Config, implementations: List<Any>) = Baker(InMemoryBaker.java(config, implementations))
}
