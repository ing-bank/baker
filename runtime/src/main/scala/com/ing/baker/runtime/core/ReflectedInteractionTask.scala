package com.ing.baker.runtime.core

import java.util.UUID

import com.ing.baker.il.petrinet.{FiresOneOfEvents, InteractionTransition, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.il.{EventType, IngredientType, processIdName}
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor, PojoEventExtractor}
import org.slf4j.{LoggerFactory, MDC}

import scala.util.Try

object ReflectedInteractionTask {

  val log = LoggerFactory.getLogger(ReflectedInteractionTask.getClass)

  val eventExtractor: EventExtractor = new PojoEventExtractor()

  def implementationsToProviderMap(implementations: Seq[AnyRef]) : Map[String, AnyRef] = {
    implementations.flatMap(im => getPossibleInteractionNamesForImplementation(im).map(_ -> im)).toMap
  }

  /**
    * This method looks for any valid name that this interaction implements
    * This is its own class name
    * The class name of any interface it implements
    * The value of the field "name"
    * @param obj
    * @return List of possible interaction names this obj can be implementing
    */
  def getPossibleInteractionNamesForImplementation(obj: Any) : Set[String] = {
    val nameField: String = Try{
      obj.getClass.getDeclaredField("name")
    }.toOption match {
      case Some(field) if field.getType == classOf[String]  => {
        field.setAccessible(true)
        field.get(obj).asInstanceOf[String]
      }
      case None => ""
    }
    val interfaceNames: Seq[String] = obj.getClass.getInterfaces.map(_.getSimpleName).toSeq
    Set[String](obj.getClass.getSimpleName, nameField).filterNot(s => s equals "") ++ interfaceNames
  }

  def createInteractionFunctions(interactions: Set[InteractionTransition[_]], implementations: Map[String, AnyRef]): InteractionTransition[_] => (ProcessState => RuntimeEvent) = {

    val implementationErrors = checkIfValidImplementationsProvided(implementations, interactions)
    if(implementationErrors.nonEmpty)
      throw new BakerException(implementationErrors.mkString(", "))

    (i: InteractionTransition[_]) => ReflectedInteractionTask.interactionTask(i.asInstanceOf[InteractionTransition[AnyRef]], () => implementations.apply(i.originalInteractionName))
  }

  private def checkIfImplementationIsValidForInteraction(implementation: AnyRef, interaction: InteractionTransition[_]): Boolean ={
    Try {
      implementation.getClass.getMethod("apply", interaction.inputFields.map(_._2): _*)
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
    }}.toSeq

    missingImplementations ++ invalidImplementations
  }

  def interactionTask[I](interaction: InteractionTransition[I], interactionProvider: () => I): ProcessState => RuntimeEvent = processState => {

    val inputArgs = createMethodInput(interaction, processState)
    val invocationId = UUID.randomUUID().toString
    val interactionObject: I = interactionProvider.apply()

    log.trace(s"[$invocationId] invoking '${interaction.originalInteractionName}' with parameters ${inputArgs.toString}")

    def invokeMethod(): AnyRef = {
      MDC.put("processId", processState.id.toString)
      val result = interactionObject.getClass.getMethod("apply", interaction.inputFields.map(_._2): _*) .invoke(interactionObject, inputArgs: _*)
      log.trace(s"[$invocationId] result: $result")

      MDC.remove("processId")
      result
    }

    def createRuntimeEvent(output: Any): RuntimeEvent = {
      interaction.providesType match {
        case FiresOneOfEvents(_, originalEvents) =>
        {
          val optionalFoundEvent: Option[EventType] = originalEvents.find(e => e.name equals output.getClass.getSimpleName)
          if (optionalFoundEvent.isDefined)
            eventExtractor.extractEvent(output).validate(optionalFoundEvent.get)
          else {
            val msg: String = s"Output: $output fired by an interaction but could not link it to any known event for the interaction"
            log.error(msg)
            throw new FatalBakerException(msg)
          }
        }
        case ProvidesIngredient(ingredient) => runtimeEventForIngredient(interaction.interactionName, output, ingredient)
        case ProvidesNothing => RuntimeEvent(s"${interaction.interactionName}:ProvidedNothing", Map.empty)
      }
    }

    createRuntimeEvent(invokeMethod())
  }

  def runtimeEventForIngredient(firedInteractionName: String, providedIngredient: Any, ingredientToComplyTo: IngredientType): RuntimeEvent = {
    if(ingredientToComplyTo.clazz.isAssignableFrom(providedIngredient.getClass))
      RuntimeEvent(s"$firedInteractionName:${ingredientToComplyTo.name}", Map(ingredientToComplyTo.name -> providedIngredient))
    //TODO Decide what to do when the ingredient is not of the correct typing, for now a Ingredient is create with a null value
    else {
      log.error(
        s"""
           |Ingredient: ${ingredientToComplyTo.name} provided by an interaction but does not comply to the expected type
           |Expected  : $ingredientToComplyTo
           |Provided  : $providedIngredient
         """.stripMargin)
      RuntimeEvent(s"$firedInteractionName:${ingredientToComplyTo.name}", Map(ingredientToComplyTo.name -> null))
    }
  }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createMethodInput[A](interaction: InteractionTransition[A], state: ProcessState): Seq[AnyRef] = {

    // We support both UUID and String types
    val processId: Option[(String, AnyRef)] = interaction.inputFields.toMap.get(processIdName).map {
      case c if c == classOf[String] => state.id.toString
      case c if c == classOf[java.util.UUID] => state.id
      case _ => throw new IllegalStateException("Type not supported")
    }.map(value => processIdName -> value)

    // parameterNamesToValues overwrites mapped token values which overwrites context map (in order of importance)
    val argumentNamesToValues: Map[String, Any] = interaction.predefinedParameters ++ processId ++ state.ingredients

    def notFound = (name: String) => {
      log.warn(
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Required input   : ${interaction.inputFieldNames.toSeq.sorted.mkString(",")}
           |Provided input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin)
      throw new IllegalArgumentException(s"Missing parameter: $name")
    }

    // map the values to the input places, throw an error if a value is not found
    val methodInput: Seq[Any] =
      interaction.inputFieldNames.map(i =>
        argumentNamesToValues.getOrElse(i, notFound))

    methodInput.map(_.asInstanceOf[AnyRef])
  }
}
