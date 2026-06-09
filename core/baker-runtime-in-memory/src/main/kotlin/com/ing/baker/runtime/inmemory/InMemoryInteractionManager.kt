package com.ing.baker.runtime.inmemory

import cats.effect.IO
import com.ing.baker.runtime.model.InteractionInstance
import com.ing.baker.runtime.model.InteractionManager
import scala.collection.immutable.List as ScalaList

class InMemoryInteractionManager(private val implementations: ScalaList<InteractionInstance<IO<*>>>): InteractionManager<IO<*>> {

    override fun allowSupersetForOutputTypes(): Boolean = false

    override fun listAll(): IO<ScalaList<InteractionInstance<IO<*>>>> = IO.pure(implementations)
}
