package com.ing.baker.runtime.akka.internal

import akka.actor.{ActorSystem, ExtendedActorSystem, Extension, ExtensionId, ExtensionIdProvider}
import com.ing.baker.runtime.model.InteractionInstrumentation

import java.util.concurrent.atomic.AtomicReference

/**
  * Holds the [[InteractionInstrumentation]] used for interactions executed by the actors of an [[ActorSystem]].
  *
  * The instrumentation is published here by the Baker implementation that owns the actor system and read by
  * [[com.ing.baker.runtime.akka.actor.process_index.ProcessIndex]], which avoids threading it through the public
  * `BakerActorProvider` and `ProcessIndex.props` signatures.
  *
  * Defaults to [[InteractionInstrumentation.noop()]], so an actor system that was never configured behaves exactly
  * as before.
  */
class BakerInstrumentation extends Extension {

  private val instrumentationRef: AtomicReference[InteractionInstrumentation] =
    new AtomicReference[InteractionInstrumentation](InteractionInstrumentation.noop())

  def instrumentation: InteractionInstrumentation = instrumentationRef.get()

  def set(instrumentation: InteractionInstrumentation): Unit =
    instrumentationRef.set(if (instrumentation == null) InteractionInstrumentation.noop() else instrumentation)

  def reset(): Unit = instrumentationRef.set(InteractionInstrumentation.noop())
}

object BakerInstrumentation extends ExtensionId[BakerInstrumentation] with ExtensionIdProvider {

  override def lookup: ExtensionId[_ <: Extension] = BakerInstrumentation

  override def createExtension(system: ExtendedActorSystem): BakerInstrumentation = new BakerInstrumentation

  override def get(system: ActorSystem): BakerInstrumentation = super.get(system)
}
