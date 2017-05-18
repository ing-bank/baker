package com.ing.baker.runtime.core

import akka.actor.ActorSystem
import akka.util.Timeout
import com.ing.baker.runtime.actor.Util
import com.ing.baker.runtime.recipe.CompiledRecipe
import io.kagera.akka.actor.PetriNetInstance
import com.ing.baker.runtime.core.EventRecovery._

object BakerTestUtil extends BakerTestUtil

trait BakerTestUtil {

  def provisionProcessWithEvents(processId: java.util.UUID, compiledRecipe: CompiledRecipe, events: List[Event])(implicit actorSystem: ActorSystem, timeout: Timeout = defaultTimeout): Unit = {
    val petriNetEvents = transformToKageraEvents(processId, events, compiledRecipe)
    val serializableEvents = serializeEvents(compiledRecipe, petriNetEvents)
    Util.persistEventsForActor(PetriNetInstance.processId2PersistenceId(processId.toString), serializableEvents)
  }
}
