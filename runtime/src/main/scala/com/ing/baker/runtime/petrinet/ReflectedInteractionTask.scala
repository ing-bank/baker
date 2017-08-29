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

  val eventExtractor: EventExtractor = new PojoEventExtractor()

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

  def createInteractionFunctions(interactions: Set[InteractionTransition[_]], implementations: Map[String, AnyRef]): InteractionTransition[_] => (ProcessState => RuntimeEvent) = {

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

  def interactionTask[I](interaction: InteractionTransition[I], interactionProvider: () => I): ProcessState => RuntimeEvent = processState => {

    val inputArgs = createMethodInput(interaction, processState)
    val invocationId = UUID.randomUUID().toString
    val interactionObject: I = interactionProvider.apply()

    log.trace(s"[$invocationId] invoking '${interaction.originalInteractionName}' with parameters ${inputArgs.toString}")

    val method = interactionObject.getClass.getMethod("apply", interaction.requiredIngredients.map { case (_, clazz) => getRawClass(clazz) }: _*)

    def invokeMethod(): AnyRef = {
      MDC.put("processId", processState.processId.toString)
      val result = method.invoke(interactionObject, inputArgs: _*)
      log.trace(s"[$invocationId] result: $result")
      MDC.remove("processId")
      result
    }

    def createRuntimeEvent(output: Any): RuntimeEvent = {
      if (interaction.providedIngredientEvent.isDefined) {
        val eventToComplyTo = interaction.providedIngredientEvent.get
        runtimeEventForIngredient(eventToComplyTo.name, output, eventToComplyTo.ingredientTypes.head)
      }
      else {
        val runtimeEvent = eventExtractor.extractEvent(output)
        if (interaction.originalEvents.exists(_ equals runtimeEvent.eventType)) {
          runtimeEvent
        }
        else {
          val msg: String = s"Output: $output fired by interaction ${interaction.interactionName} but could not link it to any known event for the interaction"
          log.error(msg)
          throw new FatalInteractionException(msg)
        }
      }
    }

    val response: AnyRef = invokeMethod()
    if (method.getReturnType.equals(Void.TYPE)) {
      if(interaction.eventsToFire.isEmpty){
        RuntimeEvent(interaction.interactionName, Seq.empty)
      }
      else {
        val msg: String = s"Void returned by interaction ${interaction.interactionName} but expected a return type"
        log.error(msg)
        throw new FatalInteractionException(msg)
      }
    }
    else createRuntimeEvent(response)
  }

  def runtimeEventForIngredient(runtimeEventName: String, providedIngredient: Any, ingredientToComplyTo: IngredientType): RuntimeEvent = {
    if (ingredientToComplyTo.clazz.isAssignableFrom(providedIngredient.getClass))
      RuntimeEvent(runtimeEventName , Seq((ingredientToComplyTo.name, providedIngredient)))
    else {
      throw new FatalInteractionException(
        s"""
           |Ingredient: ${ingredientToComplyTo.name} provided by an interaction but does not comply to the expected type
           |Expected  : ${ingredientToComplyTo.javaType}
           |Provided  : $providedIngredient
         """.stripMargin)
    }
  }

  /**
    * Convert place names which are the same as argument names to actual parameter values.
    *
    * @return Sequence of values in order of argument lists
    */
  def createMethodInput[A](interaction: InteractionTransition[A], state: ProcessState): Seq[AnyRef] = {

    // We do not support any other type then String types
    val processId: (String, String) = processIdName -> state.processId.toString

    // parameterNamesToValues overwrites mapped token values which overwrites context map (in order of importance)
    val argumentNamesToValues: Map[String, Any] = interaction.predefinedParameters ++ state.ingredients + processId

    def notFound = (name: String) => {
      log.warn(
        s"""
           |IllegalArgumentException at Interaction: $toString
           |Missing parameter: $name
           |Required input   : ${interaction.requiredIngredients.toMap.keySet.toSeq.sorted.mkString(",")}
           |Provided input   : ${argumentNamesToValues.keySet.toSeq.sorted.mkString(",")}
         """.stripMargin)
      throw new IllegalArgumentException(s"Missing parameter: $name")
    }

    def autoBoxIfNeeded(ingredientName: String, ingredientType: java.lang.reflect.Type, value: Any) = {
      val ingredientClass = getRawClass(ingredientType)

      if (autoBoxClasses.contains(ingredientClass) && !ingredientClass.isAssignableFrom(value.getClass))
        autoBoxClasses(ingredientClass).apply(value)
      else
       value
    }


    // map the values to the input places, throw an error if a value is not found
    val methodInput: Seq[Any] =
      interaction.requiredIngredients.map {
        case (ingredientName, ingredientType) =>

          val value = argumentNamesToValues.getOrElse(ingredientName, notFound)
          autoBoxIfNeeded(ingredientName, ingredientType, value)
      }

    methodInput.map(_.asInstanceOf[AnyRef])
  }
}
