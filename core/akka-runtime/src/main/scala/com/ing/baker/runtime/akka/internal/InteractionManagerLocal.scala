package com.ing.baker.runtime.akka.internal

import java.util.concurrent.ConcurrentHashMap

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.compat.java8.FunctionConverters._
import scala.concurrent.Future

/**
  * The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  *
  * @param interactionImplementations All
  */
class InteractionManagerLocal(private var interactionImplementations: Seq[InteractionInstance] = Seq.empty) extends InteractionManager {

  private val implementationCache: ConcurrentHashMap[InteractionTransition, InteractionInstance] =
    new ConcurrentHashMap[InteractionTransition, InteractionInstance]

  def addImplementation(implementation: InteractionInstance): Future[Unit] =
    Future.successful(interactionImplementations :+= implementation)

  override def getImplementation(interaction: InteractionTransition): Future[Option[InteractionInstance]] = {
    def findInteractionImplementation(interaction: InteractionTransition): InteractionInstance =
      interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation)).orNull
    Future.successful(Option(implementationCache.computeIfAbsent(interaction, (findInteractionImplementation _).asJava)))
  }
}
