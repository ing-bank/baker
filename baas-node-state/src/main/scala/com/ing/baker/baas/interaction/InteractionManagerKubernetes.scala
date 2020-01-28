package com.ing.baker.baas.interaction

import java.util.concurrent.ConcurrentHashMap

import akka.actor.ActorSystem
import akka.stream.Materializer
import akka.util.Timeout
import com.ing.baker.baas.akka.RemoteInteractionClient
import com.ing.baker.baas.state.KubernetesFunctions
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.internal.{FatalInteractionException, InteractionManager}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
import com.ing.baker.runtime.serialization.Encryption

import scala.concurrent.Future
import cats.implicits._
import scala.compat.java8.FunctionConverters._

class InteractionManagerKubernetes(postTimeout: Timeout, computationTimeout: Timeout)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends InteractionManager {

  //TODO changes this to an Actor

  import system.dispatcher

  def loadInteractions: Future[List[InteractionInstance]] = {
    KubernetesFunctions
      .getInteractionAddresses()
      .map(RemoteInteractionClient(_))
      .toList
      .traverse(client => client.interface.map {
        case (name, types) => InteractionInstance(
          name = name,
          input = types,
          run = client.apply
        )
      })
  }

  private var interactionImplementations: Seq[InteractionInstance] = Seq.empty

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
          implementation.input.exists(_.isAssignableFrom(descriptor.`type`))
        }
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }

  private def findInteractionImplementation(interaction: InteractionTransition): InteractionInstance =
    interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation)).orNull

  override def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {
    this.getImplementation(interaction) match {
      case Some(implementation) => implementation.run(input)
      case None => Future.failed(new FatalInteractionException("No implementation available for interaction"))
    }
  }

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
  private[interaction] def getImplementation(interaction: InteractionTransition): Option[InteractionInstance] =
    Option(implementationCache.computeIfAbsent(interaction, (findInteractionImplementation _).asJava))

  def hasImplementation(interaction: InteractionTransition): Future[Boolean] =
    Future.successful(getImplementation(interaction).isDefined)

  override def addImplementation(interaction: InteractionInstance): Future[Unit] =
    Future.failed(new IllegalStateException("Adding implmentation instances is not supported on a BaaS cluster"))

}
