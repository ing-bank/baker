package com.ing.baker.runtime.recipe

import akka.actor.ActorSystem
import akka.serialization.SerializationExtension
import com.ing.baker.runtime.core.NonSerializableException
import com.ing.baker.runtime.recipe.duplicates.ReflectionHelpers._
import com.ing.baker.runtime.recipe.transitions.InteractionTransition
import com.ing.baker.runtime.recipe.transitions.ProvidesType.ProvidesEvent

import scala.util.Try

object RecipeValidations {

  def validateInteraction(compiledRecipe: CompiledRecipe)(interaction: InteractionTransition[_]): Seq[String] = {

    val validationErrors = scala.collection.mutable.MutableList.empty[String]

    if (compiledRecipe.petriNet.inMarking(interaction).isEmpty)
      validationErrors += s"Interaction $interaction does not have any requirements (ingredients or preconditions)! This will result in an infinite execution loop."

    interaction.providesType match {
      case ProvidesEvent(outputFieldNames: Seq[String], outputType: Class[_], outputEventClasses: Seq[Class[_]]) =>
        outputEventClasses.foreach(eventClass =>
          if (outputType.isAssignableFrom(eventClass))
            validationErrors += s"Event class: $eventClass is not assignable to return type: ${outputType} for interaction: $interaction")
      case _ => ()
    }

    // check if the process id argument type is correct, TODO remove overlap with code below
    interaction.method.processIdClass.foreach {
      case c if c == classOf[String]         =>
      case c if c == classOf[java.util.UUID] =>
      case c => validationErrors += s"Non supported process id class: ${c.getName} on interaction: '$interaction'"
    }

    // throw an exception is attempting to predefine a non existing input field
    (interaction.predefinedParameters.keySet -- interaction.inputFieldNames.toSet) foreach { name =>
      validationErrors += s"Predefined argument '$name' is not defined on interaction: '$interaction'"
    }

    // check if the predefined ingredient is of the expected type
    interaction.predefinedParameters.foreach {
      case (name, value) =>
        val methodName = interaction.method.parameterTypeForName(name)
        // We do not have to add a validation error if the method name is not defined since this is validated for all given ingredients at the same time
        if(methodName.isDefined){
          val parameterType = interaction.method.parameterTypeForName(name).get
          if (!parameterType.isInstance(value))
            validationErrors += s"Predefined argument '$name' is not of type: $parameterType on interaction: '$interaction'"
        }
    }

    validationErrors
  }

  def validateInteractions(compiledRecipe: CompiledRecipe): Seq[String] =
    compiledRecipe.interactionTransitions.toSeq.flatMap(validateInteraction(compiledRecipe))

  /**
    * Validates that all required ingredients for interactions are provided for and of the correct type.
    */
  def validateInteractionIngredients(compiledRecipe: CompiledRecipe): Seq[String] = {
    compiledRecipe.interactionTransitions.toSeq.flatMap { t =>
      t.requiredIngredients.flatMap {
        case (name, expectedType) =>
          compiledRecipe.ingredients.get(name) match {
            case None =>
              Some(
                s"Ingredient '$name' for interaction '${t.interactionClass}:${t.method.getName}' is not provided by any event or interaction")
            case Some(providedType) if !expectedType.isAssignableFrom(providedType) =>
              Some(
                s"Interaction '$t' expects ingredient '$name:$expectedType', however incompatible type: '$providedType' was provided")
            case _ =>
              None
          }
      }
    }
  }

  //TODO decide if we really want to check this? Is only of type Event valid for the runtime?
  def validateEventsExtendFromBakerEvent(compiledRecipe: CompiledRecipe): Seq[String] = {
    // check all event classes (sensory events + interaction events)
//    val eventValidationsErrors = compiledRecipe.allEvents.toSeq
//      .filter(c => !classOf[Event].isAssignableFrom(c))
//      .map(c => s"Event class: $c does not extend from com.ing.baker.api.Event")
//
//    // check all interactions that provide an ingredient (instead of an event)
////    val interactionIngredientsValidationsErrors = compiledRecipe.interactionTransitions.toSeq
////      .filter(_.providesIngredient)
////      .map(_.method.getReturnType)
////      .filter(c => !classOf[java.io.Serializable].isAssignableFrom(c))
////      .map(c => s"Ingredient class: $c does not extend from java.io.Serializable")
////    eventValidationsErrors ++ interactionIngredientsValidationsErrors
//    eventValidationsErrors
    Seq.empty
  }

  def validateNoCycles(compiledRecipe: CompiledRecipe): Seq[String] =
    compiledRecipe.petriNet.innerGraph.findCycle
      .map(c => s"The petri net topology contains a cycle: $c")
      .toSeq

  /**
    * Validates the compiled recipe.
    *
    * The validations are:
    *   1. Validate that an implementation is provided for the interaction
    *   2. Validate that the return type the interaction matches the expectations from the annotation
    *   3. Check if all the required events are provided
    *   4. Check if all ingredients are provided
    *   5. Check if the provided ingredients are of the same type as the expected ingredients
    */
  def postCompileValidations(compiledRecipe: CompiledRecipe,
                             validationSettings: ValidationSettings): CompiledRecipe = {

    // TODO don't use a mutable list but instead a more functional solutions such as folding or a writer monad
    val postCompileValidationErrors = scala.collection.mutable.MutableList.empty[String]

    postCompileValidationErrors ++= validateInteractionIngredients(compiledRecipe)
    postCompileValidationErrors ++= validateInteractions(compiledRecipe)
    postCompileValidationErrors ++= validateEventsExtendFromBakerEvent(compiledRecipe)

    if (!validationSettings.allowCycles)
    postCompileValidationErrors ++= validateNoCycles(compiledRecipe)

    if (!validationSettings.allowDisconnectedness && !compiledRecipe.petriNet.innerGraph.isConnected)
    postCompileValidationErrors += "The petri net topology is not completely connected"

    compiledRecipe.copy(
      validationErrors = compiledRecipe.validationErrors ++ postCompileValidationErrors)
  }

  @throws[NonSerializableException]
  def assertEventsAndIngredientsAreSerializable(compiledRecipe: CompiledRecipe)(implicit actorSystem: ActorSystem): Unit = {
    val serialization = SerializationExtension(actorSystem)

    val hasAkkaSerializer = (clazz: Class[_]) => Try { serialization.serializerFor(clazz) }.isSuccess

    // check all event classes (sensory events + interaction events)
    val eventSerializationErrors: Seq[String] = compiledRecipe.allEvents.toSeq
      .filterNot(hasAkkaSerializer)
      .map(c => s"Event class: $c is not serializable by akka")

    val ingredientSerializationErrors: Seq[String] =
      compiledRecipe.ingredients
        .filterNot{case (c, v) => hasAkkaSerializer(v) }
        .map{case (c, v) => s"Ingredient $c of $v is not serializable by akka"}.toSeq

    val allErrors: Seq[String] = eventSerializationErrors ++ ingredientSerializationErrors

    if (allErrors.nonEmpty) throw new NonSerializableException(allErrors.mkString(", "))
  }
}
