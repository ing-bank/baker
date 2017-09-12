package com.ing.baker.runtime.petrinet

import java.util.UUID

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{IngredientType, processIdName, _}
import com.ing.baker.runtime.core.{BakerException, ProcessState, RuntimeEvent}
import com.ing.baker.runtime.event_extractors.{EventExtractor, PojoEventExtractor}
import org.slf4j.{LoggerFactory, MDC}

import scala.util.Try

object ReflectedInteractionTask {

  val log = LoggerFactory.getLogger(ReflectedInteractionTask.getClass)

  def implementationsToProviderMap(implementations: Seq[AnyRef]): Map[String, AnyRef] = {
    implementations.flatMap(im => getPossibleInteractionNamesForImplementation(im).map(_ -> im)).toMap
  }

  /**
    * This method looks for any valid name that this interaction implements
    * This is its own class name
    * The class name of any interface it implements
    * The value of the field "name"
    *
    * @param obj
    * @return List of possible interaction names this obj can be implementing
    */
  def getPossibleInteractionNamesForImplementation(obj: Any): Set[String] = {
    val nameField: String = Try {
      obj.getClass.getDeclaredField("name")
    }.toOption match {
      case Some(field) if field.getType == classOf[String] => {
        field.setAccessible(true)
        field.get(obj).asInstanceOf[String]
      }
      case None => ""
    }
    val interfaceNames: Seq[String] = obj.getClass.getInterfaces.map(_.getSimpleName).toSeq
    Set[String](obj.getClass.getSimpleName, nameField).filterNot(s => s equals "") ++ interfaceNames
  }

  def createInteractionFunctions(interactions: Set[InteractionTransition[_]], implementations: Map[String, AnyRef]): InteractionTransition[_] => (Seq[Any] => Any) = {

    val implementationErrors = checkIfValidImplementationsProvided(implementations, interactions)
    if (implementationErrors.nonEmpty)
      throw new BakerException(implementationErrors.mkString(", "))

    (i: InteractionTransition[_]) => ReflectedInteractionTask.interactionTask(i.asInstanceOf[InteractionTransition[AnyRef]], () => implementations.apply(i.originalInteractionName))
  }

  private def checkIfImplementationIsValidForInteraction(implementation: AnyRef, interaction: InteractionTransition[_]): Boolean = {
    Try {
      implementation.getClass.getMethod("apply", interaction.requiredIngredients.map { case (_, clazz) => getRawClass(clazz) }: _*)
    }.isSuccess
  }

  private def checkIfValidImplementationsProvided(implementations: Map[String, AnyRef], actions: Set[InteractionTransition[_]]): Set[String] = {
    //Check if all implementations are provided
    val missingImplementations: Set[String] = actions.filterNot(i => implementations.contains(i.originalInteractionName))
      .map(i => s"No implementation provided for interaction: ${i.originalInteractionName}")

    //Check if the provided implementations are valid
    val neededImplementations: Map[String, AnyRef] = implementations.filterKeys(s => actions.exists(i => s equals i.originalInteractionName))
    val invalidImplementations: Seq[String] = neededImplementations.flatMap { case (neededInteractionName, impl) => {
      if (checkIfImplementationIsValidForInteraction(impl, actions.find(_.originalInteractionName == neededInteractionName).get)) None
      else Some(s"Invalid implementation provided for interaction: $neededInteractionName")
    }
    }.toSeq

    missingImplementations ++ invalidImplementations
  }

  def interactionTask[I](interaction: InteractionTransition[I], interactionProvider: () => I): Seq[Any] => Any = inputArgs => {

    val invocationId = UUID.randomUUID().toString
    val interactionObject: I = interactionProvider.apply()

    log.trace(s"[$invocationId] invoking '${interaction.originalInteractionName}' with parameters ${inputArgs.toString}")

    val method = interactionObject.getClass.getMethod("apply", interaction.requiredIngredients.map { case (_, clazz) => getRawClass(clazz) }: _*)

    val result = method.invoke(interactionObject, inputArgs.asInstanceOf[Seq[AnyRef]]: _*)
    log.trace(s"[$invocationId] result: $result")
    result
  }
}
