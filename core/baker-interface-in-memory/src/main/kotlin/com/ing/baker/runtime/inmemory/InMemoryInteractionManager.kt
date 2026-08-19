package com.ing.baker.runtime.inmemory

import com.ing.baker.runtime.model.InteractionInstance
import com.ing.baker.runtime.model.InteractionManager
import scala.collection.immutable.List as ScalaList

class InMemoryInteractionManager(
    private val implementations: ScalaList<InteractionInstance<InMemoryEffect<*>>>
): InteractionManager<InMemoryEffect<*>> {

    override fun allowSupersetForOutputTypes(): Boolean = false

    override fun listAll(): InMemoryEffect<ScalaList<InteractionInstance<InMemoryEffect<*>>>> =
        InMemoryEffects.pure(implementations)
}
