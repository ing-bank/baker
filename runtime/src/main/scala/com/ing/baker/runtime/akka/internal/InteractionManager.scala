package com.ing.baker.runtime.akka.internal

import java.util.concurrent.ConcurrentHashMap

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.compat.java8.FunctionConverters._

/**
  * The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  *
  * @param interactionImplementations All
  */
class InteractionManager(private var interactionImplementations: Seq[InteractionInstance] = Seq.empty) {

  private val implementationCache: ConcurrentHashMap[InteractionTransition, InteractionInstance] =
    new ConcurrentHashMap[InteractionTransition, InteractionInstance]

  private def isCompatibleImplementation(interaction: InteractionTransition, implementation: InteractionInstance): Boolean = {
    val interactionNameMatches =
      interaction.originalInteractionName == implementation.name
    val inputSizeMatches =
      implementation.input.size == interaction.requiredIngredients.size
    val inputNamesAndTypesMatches =
      interaction
        .requiredIngredients
        .forall { descriptor =>
          implementation.input.exists(_._2.isAssignableFrom(descriptor.`type`))
        }
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }

  private def findInteractionImplementation(interaction: InteractionTransition): InteractionInstance =
      interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation)).orNull

  /**
    * Add an implementation to the InteractionManager
    *
    * @param implementation
    */
  def addImplementation(implementation: InteractionInstance): Unit =
    interactionImplementations :+= implementation

  /**
    * Gets an implementation is available for the given interaction.
    * It checks:
    *   1. Name
    *   2. Input variable sizes
    *   3. Input variable types
    *
    * @param interaction The interaction to check
    * @return An option containing the implementation if available
    */
  def getImplementation(interaction: InteractionTransition): Option[InteractionInstance] =
    Option(implementationCache.computeIfAbsent(interaction, (findInteractionImplementation _).asJava))
}
